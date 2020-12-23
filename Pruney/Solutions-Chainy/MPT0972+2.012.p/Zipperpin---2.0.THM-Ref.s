%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YxDcmPOZKb

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:34 EST 2020

% Result     : Theorem 2.40s
% Output     : Refutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  226 (1573 expanded)
%              Number of leaves         :   46 ( 507 expanded)
%              Depth                    :   28
%              Number of atoms          : 1588 (16030 expanded)
%              Number of equality atoms :  109 ( 819 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t18_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( r2_hidden @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ! [E: $i] :
                  ( ( r2_hidden @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8 = X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('9',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('10',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_B @ ( sk_B_1 @ ( k1_zfmisc_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_B_1 @ ( k1_zfmisc_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('21',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('22',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_relset_1 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( r2_relset_1 @ X0 @ k1_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_relset_1 @ X1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('35',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_B_2 = X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('42',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( sk_B_2 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ X0 @ sk_C_3 @ sk_D )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v1_xboole_0 @ sk_C_3 )
    | ~ ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['29','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,
    ( ~ ( v1_xboole_0 @ sk_C_3 )
    | ~ ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('51',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('54',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_C_3 )
    | ( r2_hidden @ ( sk_B @ sk_C_3 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('59',plain,
    ( ( v1_xboole_0 @ sk_C_3 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( v1_xboole_0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( v1_xboole_0 @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('64',plain,
    ( ( v1_xboole_0 @ sk_C_3 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('66',plain,
    ( ( v1_xboole_0 @ sk_C_3 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('68',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_B_1 @ ( k1_zfmisc_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('70',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('71',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('72',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( sk_B_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('75',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( sk_B_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( sk_B_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('78',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('79',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_relat_1 @ ( sk_B_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( sk_B_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) @ X0 ) ),
    inference(demod,[status(thm)],['76','81'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('83',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ ( sk_B_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['69','84'])).

thf('86',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['67','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['91'])).

thf('93',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_3 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['66','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('95',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('96',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','96'])).

thf('98',plain,
    ( ( v1_xboole_0 @ sk_C_3 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('99',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('101',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_3 ) ),
    inference(clc,[status(thm)],['93','101'])).

thf('103',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['49','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('105',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('106',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_B @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('111',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['104','111'])).

thf('113',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('116',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('118',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['103','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','28'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('122',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('124',plain,
    ( ( zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_B_2 = X0 )
      | ( zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','124'])).

thf('126',plain,(
    v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('128',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('131',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['128','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( sk_B_2 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['125','132'])).

thf('134',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ X0 @ sk_C_3 @ sk_D )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ~ ( v1_xboole_0 @ sk_C_3 )
    | ~ ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['120','135'])).

thf('137',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('138',plain,
    ( ~ ( v1_xboole_0 @ sk_C_3 )
    | ~ ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_3 ) ),
    inference(clc,[status(thm)],['93','101'])).

thf('140',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('142',plain,
    ( ( zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('143',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['128','131'])).

thf('145',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(clc,[status(thm)],['140','145'])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('147',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X19 = X18 )
      | ( r2_hidden @ ( sk_C_2 @ X18 @ X19 ) @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ X19 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_3 )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_C_3 ) @ ( k1_relat_1 @ sk_C_3 ) )
      | ( sk_C_3 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('151',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(clc,[status(thm)],['140','145'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_C_3 ) @ sk_A )
      | ( sk_C_3 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['148','151','152','153'])).

thf('155',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_3 = sk_D )
    | ( r2_hidden @ ( sk_C_2 @ sk_D @ sk_C_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['119','154'])).

thf('156',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('158',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_3 = sk_D )
    | ( r2_hidden @ ( sk_C_2 @ sk_D @ sk_C_3 ) @ sk_A ) ),
    inference(demod,[status(thm)],['155','158','159'])).

thf('161',plain,
    ( ( r2_hidden @ ( sk_C_2 @ sk_D @ sk_C_3 ) @ sk_A )
    | ( sk_C_3 = sk_D ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    ! [X41: $i] :
      ( ( ( k1_funct_1 @ sk_C_3 @ X41 )
        = ( k1_funct_1 @ sk_D @ X41 ) )
      | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( sk_C_3 = sk_D )
    | ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_D @ sk_C_3 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_2 @ sk_D @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_D @ sk_C_3 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_2 @ sk_D @ sk_C_3 ) ) ),
    inference(condensation,[status(thm)],['163'])).

thf('165',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X19 = X18 )
      | ( ( k1_funct_1 @ X19 @ ( sk_C_2 @ X18 @ X19 ) )
       != ( k1_funct_1 @ X18 @ ( sk_C_2 @ X18 @ X19 ) ) )
      | ( ( k1_relat_1 @ X19 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('166',plain,
    ( ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_D @ sk_C_3 ) )
     != ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_D @ sk_C_3 ) ) )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ( ( k1_relat_1 @ sk_C_3 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_3 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['149','150'])).

thf('168',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(clc,[status(thm)],['140','145'])).

thf('170',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['103','118'])).

thf('171',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['156','157'])).

thf('173',plain,
    ( ( ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_D @ sk_C_3 ) )
     != ( k1_funct_1 @ sk_C_3 @ ( sk_C_2 @ sk_D @ sk_C_3 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_3 = sk_D ) ),
    inference(demod,[status(thm)],['166','167','168','169','170','171','172'])).

thf('174',plain,(
    sk_C_3 = sk_D ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['22'])).

thf('177',plain,(
    r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 @ sk_C_3 ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    $false ),
    inference(demod,[status(thm)],['0','174','177'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YxDcmPOZKb
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:21:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 2.40/2.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.40/2.66  % Solved by: fo/fo7.sh
% 2.40/2.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.40/2.66  % done 3009 iterations in 2.163s
% 2.40/2.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.40/2.66  % SZS output start Refutation
% 2.40/2.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.40/2.66  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 2.40/2.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.40/2.66  thf(sk_C_3_type, type, sk_C_3: $i).
% 2.40/2.66  thf(sk_B_type, type, sk_B: $i > $i).
% 2.40/2.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.40/2.66  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.40/2.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.40/2.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.40/2.66  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 2.40/2.66  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.40/2.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.40/2.66  thf(sk_D_type, type, sk_D: $i).
% 2.40/2.66  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.40/2.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.40/2.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.40/2.66  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.40/2.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.40/2.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.40/2.66  thf(sk_A_type, type, sk_A: $i).
% 2.40/2.66  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.40/2.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.40/2.66  thf(sk_B_2_type, type, sk_B_2: $i).
% 2.40/2.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.40/2.66  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.40/2.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.40/2.66  thf(t18_funct_2, conjecture,
% 2.40/2.66    (![A:$i,B:$i,C:$i]:
% 2.40/2.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.40/2.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.40/2.66       ( ![D:$i]:
% 2.40/2.66         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.40/2.66             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.40/2.66           ( ( ![E:$i]:
% 2.40/2.66               ( ( r2_hidden @ E @ A ) =>
% 2.40/2.66                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 2.40/2.66             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 2.40/2.66  thf(zf_stmt_0, negated_conjecture,
% 2.40/2.66    (~( ![A:$i,B:$i,C:$i]:
% 2.40/2.66        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.40/2.66            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.40/2.66          ( ![D:$i]:
% 2.40/2.66            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.40/2.66                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.40/2.66              ( ( ![E:$i]:
% 2.40/2.66                  ( ( r2_hidden @ E @ A ) =>
% 2.40/2.66                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 2.40/2.66                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 2.40/2.66    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 2.40/2.66  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 @ sk_D)),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.66  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.40/2.66  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.40/2.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.40/2.66  thf(t2_tarski, axiom,
% 2.40/2.66    (![A:$i,B:$i]:
% 2.40/2.66     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 2.40/2.66       ( ( A ) = ( B ) ) ))).
% 2.40/2.66  thf('2', plain,
% 2.40/2.66      (![X7 : $i, X8 : $i]:
% 2.40/2.66         (((X8) = (X7))
% 2.40/2.66          | (r2_hidden @ (sk_C_1 @ X7 @ X8) @ X7)
% 2.40/2.66          | (r2_hidden @ (sk_C_1 @ X7 @ X8) @ X8))),
% 2.40/2.66      inference('cnf', [status(esa)], [t2_tarski])).
% 2.40/2.66  thf(d1_xboole_0, axiom,
% 2.40/2.66    (![A:$i]:
% 2.40/2.66     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.40/2.66  thf('3', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.40/2.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.66  thf('4', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i]:
% 2.40/2.66         ((r2_hidden @ (sk_C_1 @ X0 @ X1) @ X1)
% 2.40/2.66          | ((X1) = (X0))
% 2.40/2.66          | ~ (v1_xboole_0 @ X0))),
% 2.40/2.66      inference('sup-', [status(thm)], ['2', '3'])).
% 2.40/2.66  thf('5', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.40/2.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.66  thf('6', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i]:
% 2.40/2.66         (~ (v1_xboole_0 @ X1) | ((X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 2.40/2.66      inference('sup-', [status(thm)], ['4', '5'])).
% 2.40/2.66  thf('7', plain,
% 2.40/2.66      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['1', '6'])).
% 2.40/2.66  thf('8', plain,
% 2.40/2.66      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['1', '6'])).
% 2.40/2.66  thf('9', plain,
% 2.40/2.66      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.40/2.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.66  thf(existence_m1_subset_1, axiom,
% 2.40/2.66    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 2.40/2.66  thf('10', plain, (![X12 : $i]: (m1_subset_1 @ (sk_B_1 @ X12) @ X12)),
% 2.40/2.66      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 2.40/2.66  thf(l3_subset_1, axiom,
% 2.40/2.66    (![A:$i,B:$i]:
% 2.40/2.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.40/2.66       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 2.40/2.66  thf('11', plain,
% 2.40/2.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.40/2.66         (~ (r2_hidden @ X13 @ X14)
% 2.40/2.66          | (r2_hidden @ X13 @ X15)
% 2.40/2.66          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 2.40/2.66      inference('cnf', [status(esa)], [l3_subset_1])).
% 2.40/2.66  thf('12', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i]:
% 2.40/2.66         ((r2_hidden @ X1 @ X0)
% 2.40/2.66          | ~ (r2_hidden @ X1 @ (sk_B_1 @ (k1_zfmisc_1 @ X0))))),
% 2.40/2.66      inference('sup-', [status(thm)], ['10', '11'])).
% 2.40/2.66  thf('13', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         ((v1_xboole_0 @ (sk_B_1 @ (k1_zfmisc_1 @ X0)))
% 2.40/2.66          | (r2_hidden @ (sk_B @ (sk_B_1 @ (k1_zfmisc_1 @ X0))) @ X0))),
% 2.40/2.66      inference('sup-', [status(thm)], ['9', '12'])).
% 2.40/2.66  thf('14', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.40/2.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.66  thf('15', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         ((v1_xboole_0 @ (sk_B_1 @ (k1_zfmisc_1 @ X0))) | ~ (v1_xboole_0 @ X0))),
% 2.40/2.66      inference('sup-', [status(thm)], ['13', '14'])).
% 2.40/2.66  thf('16', plain,
% 2.40/2.66      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['1', '6'])).
% 2.40/2.66  thf('17', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         (~ (v1_xboole_0 @ X0)
% 2.40/2.66          | ((sk_B_1 @ (k1_zfmisc_1 @ X0)) = (k1_xboole_0)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['15', '16'])).
% 2.40/2.66  thf('18', plain, (![X12 : $i]: (m1_subset_1 @ (sk_B_1 @ X12) @ X12)),
% 2.40/2.66      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 2.40/2.66  thf('19', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 2.40/2.66          | ~ (v1_xboole_0 @ X0))),
% 2.40/2.66      inference('sup+', [status(thm)], ['17', '18'])).
% 2.40/2.66  thf(t113_zfmisc_1, axiom,
% 2.40/2.66    (![A:$i,B:$i]:
% 2.40/2.66     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.40/2.66       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.40/2.66  thf('20', plain,
% 2.40/2.66      (![X10 : $i, X11 : $i]:
% 2.40/2.66         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 2.40/2.66          | ((X11) != (k1_xboole_0)))),
% 2.40/2.66      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.40/2.66  thf('21', plain,
% 2.40/2.66      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 2.40/2.66      inference('simplify', [status(thm)], ['20'])).
% 2.40/2.66  thf(reflexivity_r2_relset_1, axiom,
% 2.40/2.66    (![A:$i,B:$i,C:$i,D:$i]:
% 2.40/2.66     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.40/2.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.40/2.66       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 2.40/2.66  thf('22', plain,
% 2.40/2.66      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.40/2.66         ((r2_relset_1 @ X29 @ X30 @ X31 @ X31)
% 2.40/2.66          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.40/2.66          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 2.40/2.66      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 2.40/2.66  thf('23', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.40/2.66         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 2.40/2.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 2.40/2.66      inference('condensation', [status(thm)], ['22'])).
% 2.40/2.66  thf('24', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i]:
% 2.40/2.66         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.40/2.66          | (r2_relset_1 @ X0 @ k1_xboole_0 @ X1 @ X1))),
% 2.40/2.66      inference('sup-', [status(thm)], ['21', '23'])).
% 2.40/2.66  thf('25', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         (~ (v1_xboole_0 @ k1_xboole_0)
% 2.40/2.66          | (r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 2.40/2.66      inference('sup-', [status(thm)], ['19', '24'])).
% 2.40/2.66  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.40/2.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.40/2.66  thf('27', plain,
% 2.40/2.66      (![X0 : $i]: (r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 2.40/2.66      inference('demod', [status(thm)], ['25', '26'])).
% 2.40/2.66  thf('28', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i]:
% 2.40/2.66         ((r2_relset_1 @ X1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 2.40/2.66          | ~ (v1_xboole_0 @ X0))),
% 2.40/2.66      inference('sup+', [status(thm)], ['8', '27'])).
% 2.40/2.66  thf('29', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.40/2.66         ((r2_relset_1 @ X2 @ k1_xboole_0 @ X1 @ X0)
% 2.40/2.66          | ~ (v1_xboole_0 @ X0)
% 2.40/2.66          | ~ (v1_xboole_0 @ X1))),
% 2.40/2.66      inference('sup+', [status(thm)], ['7', '28'])).
% 2.40/2.66  thf('30', plain,
% 2.40/2.66      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['1', '6'])).
% 2.40/2.66  thf(d1_funct_2, axiom,
% 2.40/2.66    (![A:$i,B:$i,C:$i]:
% 2.40/2.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.40/2.66       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.40/2.66           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.40/2.66             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.40/2.66         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.40/2.66           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.40/2.66             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.40/2.66  thf(zf_stmt_1, axiom,
% 2.40/2.66    (![B:$i,A:$i]:
% 2.40/2.66     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.40/2.66       ( zip_tseitin_0 @ B @ A ) ))).
% 2.40/2.66  thf('31', plain,
% 2.40/2.66      (![X33 : $i, X34 : $i]:
% 2.40/2.66         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.66  thf('32', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.40/2.66         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | (zip_tseitin_0 @ X1 @ X2))),
% 2.40/2.66      inference('sup+', [status(thm)], ['30', '31'])).
% 2.40/2.66  thf('33', plain,
% 2.40/2.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.66  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.40/2.66  thf(zf_stmt_3, axiom,
% 2.40/2.66    (![C:$i,B:$i,A:$i]:
% 2.40/2.66     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.40/2.66       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.40/2.66  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.40/2.66  thf(zf_stmt_5, axiom,
% 2.40/2.66    (![A:$i,B:$i,C:$i]:
% 2.40/2.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.40/2.66       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.40/2.66         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.40/2.66           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.40/2.66             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.40/2.66  thf('34', plain,
% 2.40/2.66      (![X38 : $i, X39 : $i, X40 : $i]:
% 2.40/2.66         (~ (zip_tseitin_0 @ X38 @ X39)
% 2.40/2.66          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 2.40/2.66          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.40/2.66  thf('35', plain,
% 2.40/2.66      (((zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 2.40/2.66        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 2.40/2.66      inference('sup-', [status(thm)], ['33', '34'])).
% 2.40/2.66  thf('36', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         (~ (v1_xboole_0 @ X0)
% 2.40/2.66          | ((sk_B_2) = (X0))
% 2.40/2.66          | (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A))),
% 2.40/2.66      inference('sup-', [status(thm)], ['32', '35'])).
% 2.40/2.66  thf('37', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_2)),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.66  thf('38', plain,
% 2.40/2.66      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.40/2.66         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 2.40/2.66          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 2.40/2.66          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.40/2.66  thf('39', plain,
% 2.40/2.66      ((~ (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 2.40/2.66        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_2 @ sk_D)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['37', '38'])).
% 2.40/2.66  thf('40', plain,
% 2.40/2.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.66  thf(redefinition_k1_relset_1, axiom,
% 2.40/2.66    (![A:$i,B:$i,C:$i]:
% 2.40/2.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.40/2.66       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.40/2.66  thf('41', plain,
% 2.40/2.66      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.40/2.66         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 2.40/2.66          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 2.40/2.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.40/2.66  thf('42', plain,
% 2.40/2.66      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.40/2.66      inference('sup-', [status(thm)], ['40', '41'])).
% 2.40/2.66  thf('43', plain,
% 2.40/2.66      ((~ (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 2.40/2.66        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.40/2.66      inference('demod', [status(thm)], ['39', '42'])).
% 2.40/2.66  thf('44', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         (((sk_B_2) = (X0))
% 2.40/2.66          | ~ (v1_xboole_0 @ X0)
% 2.40/2.66          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['36', '43'])).
% 2.40/2.66  thf('45', plain, (~ (r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 @ sk_D)),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.66  thf('46', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         (~ (r2_relset_1 @ sk_A @ X0 @ sk_C_3 @ sk_D)
% 2.40/2.66          | ((sk_A) = (k1_relat_1 @ sk_D))
% 2.40/2.66          | ~ (v1_xboole_0 @ X0))),
% 2.40/2.66      inference('sup-', [status(thm)], ['44', '45'])).
% 2.40/2.66  thf('47', plain,
% 2.40/2.66      ((~ (v1_xboole_0 @ sk_C_3)
% 2.40/2.66        | ~ (v1_xboole_0 @ sk_D)
% 2.40/2.66        | ~ (v1_xboole_0 @ k1_xboole_0)
% 2.40/2.66        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['29', '46'])).
% 2.40/2.66  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.40/2.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.40/2.66  thf('49', plain,
% 2.40/2.66      ((~ (v1_xboole_0 @ sk_C_3)
% 2.40/2.66        | ~ (v1_xboole_0 @ sk_D)
% 2.40/2.66        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.40/2.66      inference('demod', [status(thm)], ['47', '48'])).
% 2.40/2.66  thf('50', plain,
% 2.40/2.66      (![X33 : $i, X34 : $i]:
% 2.40/2.66         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.66  thf('51', plain,
% 2.40/2.66      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 2.40/2.66      inference('simplify', [status(thm)], ['20'])).
% 2.40/2.66  thf('52', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.40/2.66         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 2.40/2.66      inference('sup+', [status(thm)], ['50', '51'])).
% 2.40/2.66  thf('53', plain,
% 2.40/2.66      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.40/2.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.66  thf('54', plain,
% 2.40/2.66      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.66  thf('55', plain,
% 2.40/2.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.40/2.66         (~ (r2_hidden @ X13 @ X14)
% 2.40/2.66          | (r2_hidden @ X13 @ X15)
% 2.40/2.66          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 2.40/2.66      inference('cnf', [status(esa)], [l3_subset_1])).
% 2.40/2.66  thf('56', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 2.40/2.66          | ~ (r2_hidden @ X0 @ sk_C_3))),
% 2.40/2.66      inference('sup-', [status(thm)], ['54', '55'])).
% 2.40/2.66  thf('57', plain,
% 2.40/2.66      (((v1_xboole_0 @ sk_C_3)
% 2.40/2.66        | (r2_hidden @ (sk_B @ sk_C_3) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['53', '56'])).
% 2.40/2.66  thf('58', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.40/2.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.66  thf('59', plain,
% 2.40/2.66      (((v1_xboole_0 @ sk_C_3)
% 2.40/2.66        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['57', '58'])).
% 2.40/2.66  thf('60', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         (~ (v1_xboole_0 @ k1_xboole_0)
% 2.40/2.66          | (zip_tseitin_0 @ sk_B_2 @ X0)
% 2.40/2.66          | (v1_xboole_0 @ sk_C_3))),
% 2.40/2.66      inference('sup-', [status(thm)], ['52', '59'])).
% 2.40/2.66  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.40/2.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.40/2.66  thf('62', plain,
% 2.40/2.66      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_2 @ X0) | (v1_xboole_0 @ sk_C_3))),
% 2.40/2.66      inference('demod', [status(thm)], ['60', '61'])).
% 2.40/2.66  thf('63', plain,
% 2.40/2.66      (((zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 2.40/2.66        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 2.40/2.66      inference('sup-', [status(thm)], ['33', '34'])).
% 2.40/2.66  thf('64', plain,
% 2.40/2.66      (((v1_xboole_0 @ sk_C_3) | (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A))),
% 2.40/2.66      inference('sup-', [status(thm)], ['62', '63'])).
% 2.40/2.66  thf('65', plain,
% 2.40/2.66      ((~ (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 2.40/2.66        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.40/2.66      inference('demod', [status(thm)], ['39', '42'])).
% 2.40/2.66  thf('66', plain, (((v1_xboole_0 @ sk_C_3) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['64', '65'])).
% 2.40/2.66  thf('67', plain,
% 2.40/2.66      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['1', '6'])).
% 2.40/2.66  thf('68', plain,
% 2.40/2.66      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.40/2.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.66  thf('69', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         (~ (v1_xboole_0 @ X0)
% 2.40/2.66          | ((sk_B_1 @ (k1_zfmisc_1 @ X0)) = (k1_xboole_0)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['15', '16'])).
% 2.40/2.66  thf('70', plain, (![X12 : $i]: (m1_subset_1 @ (sk_B_1 @ X12) @ X12)),
% 2.40/2.66      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 2.40/2.66  thf('71', plain,
% 2.40/2.66      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 2.40/2.66      inference('simplify', [status(thm)], ['20'])).
% 2.40/2.66  thf(cc2_relset_1, axiom,
% 2.40/2.66    (![A:$i,B:$i,C:$i]:
% 2.40/2.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.40/2.66       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.40/2.66  thf('72', plain,
% 2.40/2.66      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.40/2.66         ((v4_relat_1 @ X23 @ X24)
% 2.40/2.66          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 2.40/2.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.40/2.66  thf('73', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i]:
% 2.40/2.66         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.40/2.66          | (v4_relat_1 @ X1 @ X0))),
% 2.40/2.66      inference('sup-', [status(thm)], ['71', '72'])).
% 2.40/2.66  thf('74', plain,
% 2.40/2.66      (![X0 : $i]: (v4_relat_1 @ (sk_B_1 @ (k1_zfmisc_1 @ k1_xboole_0)) @ X0)),
% 2.40/2.66      inference('sup-', [status(thm)], ['70', '73'])).
% 2.40/2.66  thf(d18_relat_1, axiom,
% 2.40/2.66    (![A:$i,B:$i]:
% 2.40/2.66     ( ( v1_relat_1 @ B ) =>
% 2.40/2.66       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.40/2.66  thf('75', plain,
% 2.40/2.66      (![X16 : $i, X17 : $i]:
% 2.40/2.66         (~ (v4_relat_1 @ X16 @ X17)
% 2.40/2.66          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 2.40/2.66          | ~ (v1_relat_1 @ X16))),
% 2.40/2.66      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.40/2.66  thf('76', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         (~ (v1_relat_1 @ (sk_B_1 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 2.40/2.66          | (r1_tarski @ 
% 2.40/2.66             (k1_relat_1 @ (sk_B_1 @ (k1_zfmisc_1 @ k1_xboole_0))) @ X0))),
% 2.40/2.66      inference('sup-', [status(thm)], ['74', '75'])).
% 2.40/2.66  thf('77', plain,
% 2.40/2.66      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 2.40/2.66      inference('simplify', [status(thm)], ['20'])).
% 2.40/2.66  thf('78', plain, (![X12 : $i]: (m1_subset_1 @ (sk_B_1 @ X12) @ X12)),
% 2.40/2.66      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 2.40/2.66  thf(cc1_relset_1, axiom,
% 2.40/2.66    (![A:$i,B:$i,C:$i]:
% 2.40/2.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.40/2.66       ( v1_relat_1 @ C ) ))).
% 2.40/2.66  thf('79', plain,
% 2.40/2.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.40/2.66         ((v1_relat_1 @ X20)
% 2.40/2.66          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 2.40/2.66      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.40/2.66  thf('80', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i]:
% 2.40/2.66         (v1_relat_1 @ (sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 2.40/2.66      inference('sup-', [status(thm)], ['78', '79'])).
% 2.40/2.66  thf('81', plain, ((v1_relat_1 @ (sk_B_1 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 2.40/2.66      inference('sup+', [status(thm)], ['77', '80'])).
% 2.40/2.66  thf('82', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         (r1_tarski @ (k1_relat_1 @ (sk_B_1 @ (k1_zfmisc_1 @ k1_xboole_0))) @ 
% 2.40/2.66          X0)),
% 2.40/2.66      inference('demod', [status(thm)], ['76', '81'])).
% 2.40/2.66  thf(d3_tarski, axiom,
% 2.40/2.66    (![A:$i,B:$i]:
% 2.40/2.66     ( ( r1_tarski @ A @ B ) <=>
% 2.40/2.66       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.40/2.66  thf('83', plain,
% 2.40/2.66      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.40/2.66         (~ (r2_hidden @ X3 @ X4)
% 2.40/2.66          | (r2_hidden @ X3 @ X5)
% 2.40/2.66          | ~ (r1_tarski @ X4 @ X5))),
% 2.40/2.66      inference('cnf', [status(esa)], [d3_tarski])).
% 2.40/2.66  thf('84', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i]:
% 2.40/2.66         ((r2_hidden @ X1 @ X0)
% 2.40/2.66          | ~ (r2_hidden @ X1 @ 
% 2.40/2.66               (k1_relat_1 @ (sk_B_1 @ (k1_zfmisc_1 @ k1_xboole_0)))))),
% 2.40/2.66      inference('sup-', [status(thm)], ['82', '83'])).
% 2.40/2.66  thf('85', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i]:
% 2.40/2.66         (~ (r2_hidden @ X0 @ (k1_relat_1 @ k1_xboole_0))
% 2.40/2.66          | ~ (v1_xboole_0 @ k1_xboole_0)
% 2.40/2.66          | (r2_hidden @ X0 @ X1))),
% 2.40/2.66      inference('sup-', [status(thm)], ['69', '84'])).
% 2.40/2.66  thf('86', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.40/2.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.40/2.66  thf('87', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i]:
% 2.40/2.66         (~ (r2_hidden @ X0 @ (k1_relat_1 @ k1_xboole_0))
% 2.40/2.66          | (r2_hidden @ X0 @ X1))),
% 2.40/2.66      inference('demod', [status(thm)], ['85', '86'])).
% 2.40/2.66  thf('88', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         ((v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 2.40/2.66          | (r2_hidden @ (sk_B @ (k1_relat_1 @ k1_xboole_0)) @ X0))),
% 2.40/2.66      inference('sup-', [status(thm)], ['68', '87'])).
% 2.40/2.66  thf('89', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.40/2.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.66  thf('90', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         ((v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.40/2.66      inference('sup-', [status(thm)], ['88', '89'])).
% 2.40/2.66  thf('91', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i]:
% 2.40/2.66         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 2.40/2.66          | ~ (v1_xboole_0 @ X0)
% 2.40/2.66          | ~ (v1_xboole_0 @ X1))),
% 2.40/2.66      inference('sup+', [status(thm)], ['67', '90'])).
% 2.40/2.66  thf('92', plain,
% 2.40/2.66      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 2.40/2.66      inference('condensation', [status(thm)], ['91'])).
% 2.40/2.66  thf('93', plain,
% 2.40/2.66      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C_3) | ~ (v1_xboole_0 @ sk_D))),
% 2.40/2.66      inference('sup+', [status(thm)], ['66', '92'])).
% 2.40/2.66  thf('94', plain,
% 2.40/2.66      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['1', '6'])).
% 2.40/2.66  thf('95', plain,
% 2.40/2.66      (![X10 : $i, X11 : $i]:
% 2.40/2.66         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 2.40/2.66          | ((X10) != (k1_xboole_0)))),
% 2.40/2.66      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.40/2.66  thf('96', plain,
% 2.40/2.66      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 2.40/2.66      inference('simplify', [status(thm)], ['95'])).
% 2.40/2.66  thf('97', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i]:
% 2.40/2.66         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.40/2.66      inference('sup+', [status(thm)], ['94', '96'])).
% 2.40/2.66  thf('98', plain,
% 2.40/2.66      (((v1_xboole_0 @ sk_C_3)
% 2.40/2.66        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['57', '58'])).
% 2.40/2.66  thf('99', plain,
% 2.40/2.66      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.40/2.66        | ~ (v1_xboole_0 @ sk_A)
% 2.40/2.66        | (v1_xboole_0 @ sk_C_3))),
% 2.40/2.66      inference('sup-', [status(thm)], ['97', '98'])).
% 2.40/2.66  thf('100', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.40/2.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.40/2.66  thf('101', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C_3))),
% 2.40/2.66      inference('demod', [status(thm)], ['99', '100'])).
% 2.40/2.66  thf('102', plain, ((~ (v1_xboole_0 @ sk_D) | (v1_xboole_0 @ sk_C_3))),
% 2.40/2.66      inference('clc', [status(thm)], ['93', '101'])).
% 2.40/2.66  thf('103', plain,
% 2.40/2.66      ((((sk_A) = (k1_relat_1 @ sk_D)) | ~ (v1_xboole_0 @ sk_D))),
% 2.40/2.66      inference('clc', [status(thm)], ['49', '102'])).
% 2.40/2.66  thf('104', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.40/2.66         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 2.40/2.66      inference('sup+', [status(thm)], ['50', '51'])).
% 2.40/2.66  thf('105', plain,
% 2.40/2.66      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.40/2.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.66  thf('106', plain,
% 2.40/2.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.66  thf('107', plain,
% 2.40/2.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.40/2.66         (~ (r2_hidden @ X13 @ X14)
% 2.40/2.66          | (r2_hidden @ X13 @ X15)
% 2.40/2.66          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 2.40/2.66      inference('cnf', [status(esa)], [l3_subset_1])).
% 2.40/2.66  thf('108', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 2.40/2.66          | ~ (r2_hidden @ X0 @ sk_D))),
% 2.40/2.66      inference('sup-', [status(thm)], ['106', '107'])).
% 2.40/2.66  thf('109', plain,
% 2.40/2.66      (((v1_xboole_0 @ sk_D)
% 2.40/2.66        | (r2_hidden @ (sk_B @ sk_D) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['105', '108'])).
% 2.40/2.66  thf('110', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.40/2.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.66  thf('111', plain,
% 2.40/2.66      (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['109', '110'])).
% 2.40/2.66  thf('112', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         (~ (v1_xboole_0 @ k1_xboole_0)
% 2.40/2.66          | (zip_tseitin_0 @ sk_B_2 @ X0)
% 2.40/2.66          | (v1_xboole_0 @ sk_D))),
% 2.40/2.66      inference('sup-', [status(thm)], ['104', '111'])).
% 2.40/2.66  thf('113', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.40/2.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.40/2.66  thf('114', plain,
% 2.40/2.66      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_2 @ X0) | (v1_xboole_0 @ sk_D))),
% 2.40/2.66      inference('demod', [status(thm)], ['112', '113'])).
% 2.40/2.66  thf('115', plain,
% 2.40/2.66      (((zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 2.40/2.66        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 2.40/2.66      inference('sup-', [status(thm)], ['33', '34'])).
% 2.40/2.66  thf('116', plain,
% 2.40/2.66      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A))),
% 2.40/2.66      inference('sup-', [status(thm)], ['114', '115'])).
% 2.40/2.66  thf('117', plain,
% 2.40/2.66      ((~ (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 2.40/2.66        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.40/2.66      inference('demod', [status(thm)], ['39', '42'])).
% 2.40/2.66  thf('118', plain, (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['116', '117'])).
% 2.40/2.66  thf('119', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 2.40/2.66      inference('clc', [status(thm)], ['103', '118'])).
% 2.40/2.66  thf('120', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.40/2.66         ((r2_relset_1 @ X2 @ k1_xboole_0 @ X1 @ X0)
% 2.40/2.66          | ~ (v1_xboole_0 @ X0)
% 2.40/2.66          | ~ (v1_xboole_0 @ X1))),
% 2.40/2.66      inference('sup+', [status(thm)], ['7', '28'])).
% 2.40/2.66  thf('121', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.40/2.66         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | (zip_tseitin_0 @ X1 @ X2))),
% 2.40/2.66      inference('sup+', [status(thm)], ['30', '31'])).
% 2.40/2.66  thf('122', plain,
% 2.40/2.66      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.66  thf('123', plain,
% 2.40/2.66      (![X38 : $i, X39 : $i, X40 : $i]:
% 2.40/2.66         (~ (zip_tseitin_0 @ X38 @ X39)
% 2.40/2.66          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 2.40/2.66          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.40/2.66  thf('124', plain,
% 2.40/2.66      (((zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A)
% 2.40/2.66        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 2.40/2.66      inference('sup-', [status(thm)], ['122', '123'])).
% 2.40/2.66  thf('125', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         (~ (v1_xboole_0 @ X0)
% 2.40/2.66          | ((sk_B_2) = (X0))
% 2.40/2.66          | (zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A))),
% 2.40/2.66      inference('sup-', [status(thm)], ['121', '124'])).
% 2.40/2.66  thf('126', plain, ((v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2)),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.66  thf('127', plain,
% 2.40/2.66      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.40/2.66         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 2.40/2.66          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 2.40/2.66          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.40/2.66  thf('128', plain,
% 2.40/2.66      ((~ (zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A)
% 2.40/2.66        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_3)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['126', '127'])).
% 2.40/2.66  thf('129', plain,
% 2.40/2.66      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.66  thf('130', plain,
% 2.40/2.66      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.40/2.66         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 2.40/2.66          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 2.40/2.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.40/2.66  thf('131', plain,
% 2.40/2.66      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_3) = (k1_relat_1 @ sk_C_3))),
% 2.40/2.66      inference('sup-', [status(thm)], ['129', '130'])).
% 2.40/2.66  thf('132', plain,
% 2.40/2.66      ((~ (zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A)
% 2.40/2.66        | ((sk_A) = (k1_relat_1 @ sk_C_3)))),
% 2.40/2.66      inference('demod', [status(thm)], ['128', '131'])).
% 2.40/2.66  thf('133', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         (((sk_B_2) = (X0))
% 2.40/2.66          | ~ (v1_xboole_0 @ X0)
% 2.40/2.66          | ((sk_A) = (k1_relat_1 @ sk_C_3)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['125', '132'])).
% 2.40/2.66  thf('134', plain, (~ (r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 @ sk_D)),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.66  thf('135', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         (~ (r2_relset_1 @ sk_A @ X0 @ sk_C_3 @ sk_D)
% 2.40/2.66          | ((sk_A) = (k1_relat_1 @ sk_C_3))
% 2.40/2.66          | ~ (v1_xboole_0 @ X0))),
% 2.40/2.66      inference('sup-', [status(thm)], ['133', '134'])).
% 2.40/2.66  thf('136', plain,
% 2.40/2.66      ((~ (v1_xboole_0 @ sk_C_3)
% 2.40/2.66        | ~ (v1_xboole_0 @ sk_D)
% 2.40/2.66        | ~ (v1_xboole_0 @ k1_xboole_0)
% 2.40/2.66        | ((sk_A) = (k1_relat_1 @ sk_C_3)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['120', '135'])).
% 2.40/2.66  thf('137', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.40/2.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.40/2.66  thf('138', plain,
% 2.40/2.66      ((~ (v1_xboole_0 @ sk_C_3)
% 2.40/2.66        | ~ (v1_xboole_0 @ sk_D)
% 2.40/2.66        | ((sk_A) = (k1_relat_1 @ sk_C_3)))),
% 2.40/2.66      inference('demod', [status(thm)], ['136', '137'])).
% 2.40/2.66  thf('139', plain, ((~ (v1_xboole_0 @ sk_D) | (v1_xboole_0 @ sk_C_3))),
% 2.40/2.66      inference('clc', [status(thm)], ['93', '101'])).
% 2.40/2.66  thf('140', plain,
% 2.40/2.66      ((((sk_A) = (k1_relat_1 @ sk_C_3)) | ~ (v1_xboole_0 @ sk_D))),
% 2.40/2.66      inference('clc', [status(thm)], ['138', '139'])).
% 2.40/2.66  thf('141', plain,
% 2.40/2.66      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_2 @ X0) | (v1_xboole_0 @ sk_D))),
% 2.40/2.66      inference('demod', [status(thm)], ['112', '113'])).
% 2.40/2.66  thf('142', plain,
% 2.40/2.66      (((zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A)
% 2.40/2.66        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 2.40/2.66      inference('sup-', [status(thm)], ['122', '123'])).
% 2.40/2.66  thf('143', plain,
% 2.40/2.66      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A))),
% 2.40/2.66      inference('sup-', [status(thm)], ['141', '142'])).
% 2.40/2.66  thf('144', plain,
% 2.40/2.66      ((~ (zip_tseitin_1 @ sk_C_3 @ sk_B_2 @ sk_A)
% 2.40/2.66        | ((sk_A) = (k1_relat_1 @ sk_C_3)))),
% 2.40/2.66      inference('demod', [status(thm)], ['128', '131'])).
% 2.40/2.66  thf('145', plain,
% 2.40/2.66      (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_C_3)))),
% 2.40/2.66      inference('sup-', [status(thm)], ['143', '144'])).
% 2.40/2.66  thf('146', plain, (((sk_A) = (k1_relat_1 @ sk_C_3))),
% 2.40/2.66      inference('clc', [status(thm)], ['140', '145'])).
% 2.40/2.66  thf(t9_funct_1, axiom,
% 2.40/2.66    (![A:$i]:
% 2.40/2.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.40/2.66       ( ![B:$i]:
% 2.40/2.66         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.40/2.66           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 2.40/2.66               ( ![C:$i]:
% 2.40/2.66                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 2.40/2.66                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 2.40/2.66             ( ( A ) = ( B ) ) ) ) ) ))).
% 2.40/2.66  thf('147', plain,
% 2.40/2.66      (![X18 : $i, X19 : $i]:
% 2.40/2.66         (~ (v1_relat_1 @ X18)
% 2.40/2.66          | ~ (v1_funct_1 @ X18)
% 2.40/2.66          | ((X19) = (X18))
% 2.40/2.66          | (r2_hidden @ (sk_C_2 @ X18 @ X19) @ (k1_relat_1 @ X19))
% 2.40/2.66          | ((k1_relat_1 @ X19) != (k1_relat_1 @ X18))
% 2.40/2.66          | ~ (v1_funct_1 @ X19)
% 2.40/2.66          | ~ (v1_relat_1 @ X19))),
% 2.40/2.66      inference('cnf', [status(esa)], [t9_funct_1])).
% 2.40/2.66  thf('148', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         (((sk_A) != (k1_relat_1 @ X0))
% 2.40/2.66          | ~ (v1_relat_1 @ sk_C_3)
% 2.40/2.66          | ~ (v1_funct_1 @ sk_C_3)
% 2.40/2.66          | (r2_hidden @ (sk_C_2 @ X0 @ sk_C_3) @ (k1_relat_1 @ sk_C_3))
% 2.40/2.66          | ((sk_C_3) = (X0))
% 2.40/2.66          | ~ (v1_funct_1 @ X0)
% 2.40/2.66          | ~ (v1_relat_1 @ X0))),
% 2.40/2.66      inference('sup-', [status(thm)], ['146', '147'])).
% 2.40/2.66  thf('149', plain,
% 2.40/2.66      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.66  thf('150', plain,
% 2.40/2.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.40/2.66         ((v1_relat_1 @ X20)
% 2.40/2.66          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 2.40/2.66      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.40/2.66  thf('151', plain, ((v1_relat_1 @ sk_C_3)),
% 2.40/2.66      inference('sup-', [status(thm)], ['149', '150'])).
% 2.40/2.66  thf('152', plain, ((v1_funct_1 @ sk_C_3)),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.66  thf('153', plain, (((sk_A) = (k1_relat_1 @ sk_C_3))),
% 2.40/2.66      inference('clc', [status(thm)], ['140', '145'])).
% 2.40/2.66  thf('154', plain,
% 2.40/2.66      (![X0 : $i]:
% 2.40/2.66         (((sk_A) != (k1_relat_1 @ X0))
% 2.40/2.66          | (r2_hidden @ (sk_C_2 @ X0 @ sk_C_3) @ sk_A)
% 2.40/2.66          | ((sk_C_3) = (X0))
% 2.40/2.66          | ~ (v1_funct_1 @ X0)
% 2.40/2.66          | ~ (v1_relat_1 @ X0))),
% 2.40/2.66      inference('demod', [status(thm)], ['148', '151', '152', '153'])).
% 2.40/2.66  thf('155', plain,
% 2.40/2.66      ((((sk_A) != (sk_A))
% 2.40/2.66        | ~ (v1_relat_1 @ sk_D)
% 2.40/2.66        | ~ (v1_funct_1 @ sk_D)
% 2.40/2.66        | ((sk_C_3) = (sk_D))
% 2.40/2.66        | (r2_hidden @ (sk_C_2 @ sk_D @ sk_C_3) @ sk_A))),
% 2.40/2.66      inference('sup-', [status(thm)], ['119', '154'])).
% 2.40/2.66  thf('156', plain,
% 2.40/2.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.66  thf('157', plain,
% 2.40/2.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.40/2.66         ((v1_relat_1 @ X20)
% 2.40/2.66          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 2.40/2.66      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.40/2.66  thf('158', plain, ((v1_relat_1 @ sk_D)),
% 2.40/2.66      inference('sup-', [status(thm)], ['156', '157'])).
% 2.40/2.66  thf('159', plain, ((v1_funct_1 @ sk_D)),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.66  thf('160', plain,
% 2.40/2.66      ((((sk_A) != (sk_A))
% 2.40/2.66        | ((sk_C_3) = (sk_D))
% 2.40/2.66        | (r2_hidden @ (sk_C_2 @ sk_D @ sk_C_3) @ sk_A))),
% 2.40/2.66      inference('demod', [status(thm)], ['155', '158', '159'])).
% 2.40/2.66  thf('161', plain,
% 2.40/2.66      (((r2_hidden @ (sk_C_2 @ sk_D @ sk_C_3) @ sk_A) | ((sk_C_3) = (sk_D)))),
% 2.40/2.66      inference('simplify', [status(thm)], ['160'])).
% 2.40/2.66  thf('162', plain,
% 2.40/2.66      (![X41 : $i]:
% 2.40/2.66         (((k1_funct_1 @ sk_C_3 @ X41) = (k1_funct_1 @ sk_D @ X41))
% 2.40/2.66          | ~ (r2_hidden @ X41 @ sk_A))),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.66  thf('163', plain,
% 2.40/2.66      ((((sk_C_3) = (sk_D))
% 2.40/2.66        | ((k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_D @ sk_C_3))
% 2.40/2.66            = (k1_funct_1 @ sk_D @ (sk_C_2 @ sk_D @ sk_C_3))))),
% 2.40/2.66      inference('sup-', [status(thm)], ['161', '162'])).
% 2.40/2.66  thf('164', plain,
% 2.40/2.66      (((k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_D @ sk_C_3))
% 2.40/2.66         = (k1_funct_1 @ sk_D @ (sk_C_2 @ sk_D @ sk_C_3)))),
% 2.40/2.66      inference('condensation', [status(thm)], ['163'])).
% 2.40/2.66  thf('165', plain,
% 2.40/2.66      (![X18 : $i, X19 : $i]:
% 2.40/2.66         (~ (v1_relat_1 @ X18)
% 2.40/2.66          | ~ (v1_funct_1 @ X18)
% 2.40/2.66          | ((X19) = (X18))
% 2.40/2.66          | ((k1_funct_1 @ X19 @ (sk_C_2 @ X18 @ X19))
% 2.40/2.66              != (k1_funct_1 @ X18 @ (sk_C_2 @ X18 @ X19)))
% 2.40/2.66          | ((k1_relat_1 @ X19) != (k1_relat_1 @ X18))
% 2.40/2.66          | ~ (v1_funct_1 @ X19)
% 2.40/2.66          | ~ (v1_relat_1 @ X19))),
% 2.40/2.66      inference('cnf', [status(esa)], [t9_funct_1])).
% 2.40/2.66  thf('166', plain,
% 2.40/2.66      ((((k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_D @ sk_C_3))
% 2.40/2.66          != (k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_D @ sk_C_3)))
% 2.40/2.66        | ~ (v1_relat_1 @ sk_C_3)
% 2.40/2.66        | ~ (v1_funct_1 @ sk_C_3)
% 2.40/2.66        | ((k1_relat_1 @ sk_C_3) != (k1_relat_1 @ sk_D))
% 2.40/2.66        | ((sk_C_3) = (sk_D))
% 2.40/2.66        | ~ (v1_funct_1 @ sk_D)
% 2.40/2.66        | ~ (v1_relat_1 @ sk_D))),
% 2.40/2.66      inference('sup-', [status(thm)], ['164', '165'])).
% 2.40/2.66  thf('167', plain, ((v1_relat_1 @ sk_C_3)),
% 2.40/2.66      inference('sup-', [status(thm)], ['149', '150'])).
% 2.40/2.66  thf('168', plain, ((v1_funct_1 @ sk_C_3)),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.66  thf('169', plain, (((sk_A) = (k1_relat_1 @ sk_C_3))),
% 2.40/2.66      inference('clc', [status(thm)], ['140', '145'])).
% 2.40/2.66  thf('170', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 2.40/2.66      inference('clc', [status(thm)], ['103', '118'])).
% 2.40/2.66  thf('171', plain, ((v1_funct_1 @ sk_D)),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.66  thf('172', plain, ((v1_relat_1 @ sk_D)),
% 2.40/2.66      inference('sup-', [status(thm)], ['156', '157'])).
% 2.40/2.66  thf('173', plain,
% 2.40/2.66      ((((k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_D @ sk_C_3))
% 2.40/2.66          != (k1_funct_1 @ sk_C_3 @ (sk_C_2 @ sk_D @ sk_C_3)))
% 2.40/2.66        | ((sk_A) != (sk_A))
% 2.40/2.66        | ((sk_C_3) = (sk_D)))),
% 2.40/2.66      inference('demod', [status(thm)],
% 2.40/2.66                ['166', '167', '168', '169', '170', '171', '172'])).
% 2.40/2.66  thf('174', plain, (((sk_C_3) = (sk_D))),
% 2.40/2.66      inference('simplify', [status(thm)], ['173'])).
% 2.40/2.66  thf('175', plain,
% 2.40/2.66      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.40/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.66  thf('176', plain,
% 2.40/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.40/2.66         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 2.40/2.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 2.40/2.66      inference('condensation', [status(thm)], ['22'])).
% 2.40/2.66  thf('177', plain, ((r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_3 @ sk_C_3)),
% 2.40/2.66      inference('sup-', [status(thm)], ['175', '176'])).
% 2.40/2.66  thf('178', plain, ($false),
% 2.40/2.66      inference('demod', [status(thm)], ['0', '174', '177'])).
% 2.40/2.66  
% 2.40/2.66  % SZS output end Refutation
% 2.40/2.66  
% 2.40/2.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C2huqLjHwF

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:35 EST 2020

% Result     : Theorem 6.36s
% Output     : Refutation 6.36s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 815 expanded)
%              Number of leaves         :   41 ( 264 expanded)
%              Depth                    :   25
%              Number of atoms          : 1221 (9726 expanded)
%              Number of equality atoms :   93 ( 466 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('16',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('24',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('39',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('40',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 )
      | ( X28 != X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('41',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_relset_1 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','43'])).

thf('45',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_D )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(condensation,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('51',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_B @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('64',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['49','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('67',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('69',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('73',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('76',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['70','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_D )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('86',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('87',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('89',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['84','89'])).

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

thf('91',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( X21 = X20 )
      | ( r2_hidden @ ( sk_C_1 @ X20 @ X21 ) @ ( k1_relat_1 @ X21 ) )
      | ( ( k1_relat_1 @ X21 )
       != ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('94',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('95',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['84','89'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['92','95','96','97'])).

thf('99',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['65','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('102',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['99','102','103'])).

thf('105',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X40: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X40 )
        = ( k1_funct_1 @ sk_D @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['107'])).

thf('109',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( X21 = X20 )
      | ( ( k1_funct_1 @ X21 @ ( sk_C_1 @ X20 @ X21 ) )
       != ( k1_funct_1 @ X20 @ ( sk_C_1 @ X20 @ X21 ) ) )
      | ( ( k1_relat_1 @ X21 )
       != ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('110',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('112',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['84','89'])).

thf('114',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['49','64'])).

thf('115',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['100','101'])).

thf('117',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['110','111','112','113','114','115','116'])).

thf('118',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_relset_1 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('121',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    $false ),
    inference(demod,[status(thm)],['0','118','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C2huqLjHwF
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:52:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.36/6.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.36/6.57  % Solved by: fo/fo7.sh
% 6.36/6.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.36/6.57  % done 4473 iterations in 6.131s
% 6.36/6.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.36/6.57  % SZS output start Refutation
% 6.36/6.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.36/6.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 6.36/6.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 6.36/6.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.36/6.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.36/6.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.36/6.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.36/6.57  thf(sk_D_type, type, sk_D: $i).
% 6.36/6.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.36/6.57  thf(sk_A_type, type, sk_A: $i).
% 6.36/6.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.36/6.57  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 6.36/6.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.36/6.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.36/6.57  thf(sk_B_type, type, sk_B: $i > $i).
% 6.36/6.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.36/6.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.36/6.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.36/6.57  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 6.36/6.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 6.36/6.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.36/6.57  thf(sk_C_2_type, type, sk_C_2: $i).
% 6.36/6.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.36/6.57  thf(t18_funct_2, conjecture,
% 6.36/6.57    (![A:$i,B:$i,C:$i]:
% 6.36/6.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.36/6.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.36/6.57       ( ![D:$i]:
% 6.36/6.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.36/6.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.36/6.57           ( ( ![E:$i]:
% 6.36/6.57               ( ( r2_hidden @ E @ A ) =>
% 6.36/6.57                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 6.36/6.57             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 6.36/6.57  thf(zf_stmt_0, negated_conjecture,
% 6.36/6.57    (~( ![A:$i,B:$i,C:$i]:
% 6.36/6.57        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.36/6.57            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.36/6.57          ( ![D:$i]:
% 6.36/6.57            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.36/6.57                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.36/6.57              ( ( ![E:$i]:
% 6.36/6.57                  ( ( r2_hidden @ E @ A ) =>
% 6.36/6.57                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 6.36/6.57                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 6.36/6.57    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 6.36/6.57  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 6.36/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.36/6.57  thf(d1_funct_2, axiom,
% 6.36/6.57    (![A:$i,B:$i,C:$i]:
% 6.36/6.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.36/6.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.36/6.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 6.36/6.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 6.36/6.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.36/6.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 6.36/6.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 6.36/6.57  thf(zf_stmt_1, axiom,
% 6.36/6.57    (![B:$i,A:$i]:
% 6.36/6.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.36/6.57       ( zip_tseitin_0 @ B @ A ) ))).
% 6.36/6.57  thf('1', plain,
% 6.36/6.57      (![X32 : $i, X33 : $i]:
% 6.36/6.57         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 6.36/6.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.36/6.57  thf(t113_zfmisc_1, axiom,
% 6.36/6.57    (![A:$i,B:$i]:
% 6.36/6.57     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 6.36/6.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 6.36/6.57  thf('2', plain,
% 6.36/6.57      (![X11 : $i, X12 : $i]:
% 6.36/6.57         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 6.36/6.57          | ((X12) != (k1_xboole_0)))),
% 6.36/6.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.36/6.57  thf('3', plain,
% 6.36/6.57      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 6.36/6.57      inference('simplify', [status(thm)], ['2'])).
% 6.36/6.57  thf('4', plain,
% 6.36/6.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.36/6.57         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 6.36/6.57      inference('sup+', [status(thm)], ['1', '3'])).
% 6.36/6.57  thf(d3_tarski, axiom,
% 6.36/6.57    (![A:$i,B:$i]:
% 6.36/6.57     ( ( r1_tarski @ A @ B ) <=>
% 6.36/6.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 6.36/6.57  thf('5', plain,
% 6.36/6.57      (![X4 : $i, X6 : $i]:
% 6.36/6.57         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 6.36/6.57      inference('cnf', [status(esa)], [d3_tarski])).
% 6.36/6.57  thf('6', plain,
% 6.36/6.57      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.36/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.36/6.57  thf(l3_subset_1, axiom,
% 6.36/6.57    (![A:$i,B:$i]:
% 6.36/6.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.36/6.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 6.36/6.57  thf('7', plain,
% 6.36/6.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 6.36/6.57         (~ (r2_hidden @ X13 @ X14)
% 6.36/6.57          | (r2_hidden @ X13 @ X15)
% 6.36/6.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 6.36/6.57      inference('cnf', [status(esa)], [l3_subset_1])).
% 6.36/6.57  thf('8', plain,
% 6.36/6.57      (![X0 : $i]:
% 6.36/6.57         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 6.36/6.57          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 6.36/6.57      inference('sup-', [status(thm)], ['6', '7'])).
% 6.36/6.57  thf('9', plain,
% 6.36/6.57      (![X0 : $i]:
% 6.36/6.57         ((r1_tarski @ sk_C_2 @ X0)
% 6.36/6.57          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.36/6.57      inference('sup-', [status(thm)], ['5', '8'])).
% 6.36/6.57  thf(d1_xboole_0, axiom,
% 6.36/6.57    (![A:$i]:
% 6.36/6.57     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 6.36/6.57  thf('10', plain,
% 6.36/6.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.36/6.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.36/6.57  thf('11', plain,
% 6.36/6.57      (![X0 : $i]:
% 6.36/6.57         ((r1_tarski @ sk_C_2 @ X0)
% 6.36/6.57          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.36/6.57      inference('sup-', [status(thm)], ['9', '10'])).
% 6.36/6.57  thf('12', plain,
% 6.36/6.57      (![X0 : $i, X1 : $i]:
% 6.36/6.57         (~ (v1_xboole_0 @ k1_xboole_0)
% 6.36/6.57          | (zip_tseitin_0 @ sk_B_1 @ X1)
% 6.36/6.57          | (r1_tarski @ sk_C_2 @ X0))),
% 6.36/6.57      inference('sup-', [status(thm)], ['4', '11'])).
% 6.36/6.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 6.36/6.57  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.36/6.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.36/6.57  thf('14', plain,
% 6.36/6.57      (![X0 : $i, X1 : $i]:
% 6.36/6.57         ((zip_tseitin_0 @ sk_B_1 @ X1) | (r1_tarski @ sk_C_2 @ X0))),
% 6.36/6.57      inference('demod', [status(thm)], ['12', '13'])).
% 6.36/6.57  thf('15', plain,
% 6.36/6.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.36/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.36/6.57  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 6.36/6.57  thf(zf_stmt_3, axiom,
% 6.36/6.57    (![C:$i,B:$i,A:$i]:
% 6.36/6.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 6.36/6.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.36/6.57  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 6.36/6.57  thf(zf_stmt_5, axiom,
% 6.36/6.57    (![A:$i,B:$i,C:$i]:
% 6.36/6.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.36/6.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 6.36/6.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.36/6.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 6.36/6.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 6.36/6.57  thf('16', plain,
% 6.36/6.57      (![X37 : $i, X38 : $i, X39 : $i]:
% 6.36/6.57         (~ (zip_tseitin_0 @ X37 @ X38)
% 6.36/6.57          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 6.36/6.57          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 6.36/6.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.36/6.57  thf('17', plain,
% 6.36/6.57      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 6.36/6.57        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 6.36/6.57      inference('sup-', [status(thm)], ['15', '16'])).
% 6.36/6.57  thf('18', plain,
% 6.36/6.57      (![X0 : $i]:
% 6.36/6.57         ((r1_tarski @ sk_C_2 @ X0) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 6.36/6.57      inference('sup-', [status(thm)], ['14', '17'])).
% 6.36/6.57  thf('19', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 6.36/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.36/6.57  thf('20', plain,
% 6.36/6.57      (![X34 : $i, X35 : $i, X36 : $i]:
% 6.36/6.57         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 6.36/6.57          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 6.36/6.57          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 6.36/6.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.36/6.57  thf('21', plain,
% 6.36/6.57      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 6.36/6.57        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 6.36/6.57      inference('sup-', [status(thm)], ['19', '20'])).
% 6.36/6.57  thf('22', plain,
% 6.36/6.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.36/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.36/6.57  thf(redefinition_k1_relset_1, axiom,
% 6.36/6.57    (![A:$i,B:$i,C:$i]:
% 6.36/6.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.36/6.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.36/6.57  thf('23', plain,
% 6.36/6.57      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.36/6.57         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 6.36/6.57          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 6.36/6.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.36/6.57  thf('24', plain,
% 6.36/6.57      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 6.36/6.57      inference('sup-', [status(thm)], ['22', '23'])).
% 6.36/6.57  thf('25', plain,
% 6.36/6.57      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 6.36/6.57        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.36/6.57      inference('demod', [status(thm)], ['21', '24'])).
% 6.36/6.57  thf('26', plain,
% 6.36/6.57      (![X0 : $i]: ((r1_tarski @ sk_C_2 @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.36/6.58      inference('sup-', [status(thm)], ['18', '25'])).
% 6.36/6.58  thf('27', plain,
% 6.36/6.58      (![X4 : $i, X6 : $i]:
% 6.36/6.58         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 6.36/6.58      inference('cnf', [status(esa)], [d3_tarski])).
% 6.36/6.58  thf('28', plain,
% 6.36/6.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.36/6.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.36/6.58  thf('29', plain,
% 6.36/6.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 6.36/6.58      inference('sup-', [status(thm)], ['27', '28'])).
% 6.36/6.58  thf(d10_xboole_0, axiom,
% 6.36/6.58    (![A:$i,B:$i]:
% 6.36/6.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.36/6.58  thf('30', plain,
% 6.36/6.58      (![X7 : $i, X9 : $i]:
% 6.36/6.58         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 6.36/6.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.36/6.58  thf('31', plain,
% 6.36/6.58      (![X0 : $i, X1 : $i]:
% 6.36/6.58         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 6.36/6.58      inference('sup-', [status(thm)], ['29', '30'])).
% 6.36/6.58  thf('32', plain,
% 6.36/6.58      (![X0 : $i]:
% 6.36/6.58         (((sk_A) = (k1_relat_1 @ sk_D))
% 6.36/6.58          | ((sk_C_2) = (X0))
% 6.36/6.58          | ~ (v1_xboole_0 @ X0))),
% 6.36/6.58      inference('sup-', [status(thm)], ['26', '31'])).
% 6.36/6.58  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.36/6.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.36/6.58  thf('34', plain,
% 6.36/6.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 6.36/6.58      inference('sup-', [status(thm)], ['27', '28'])).
% 6.36/6.58  thf('35', plain,
% 6.36/6.58      (![X0 : $i, X1 : $i]:
% 6.36/6.58         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 6.36/6.58      inference('sup-', [status(thm)], ['29', '30'])).
% 6.36/6.58  thf('36', plain,
% 6.36/6.58      (![X0 : $i, X1 : $i]:
% 6.36/6.58         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 6.36/6.58      inference('sup-', [status(thm)], ['34', '35'])).
% 6.36/6.58  thf('37', plain,
% 6.36/6.58      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 6.36/6.58      inference('sup-', [status(thm)], ['33', '36'])).
% 6.36/6.58  thf('38', plain,
% 6.36/6.58      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 6.36/6.58      inference('sup-', [status(thm)], ['33', '36'])).
% 6.36/6.58  thf(t4_subset_1, axiom,
% 6.36/6.58    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 6.36/6.58  thf('39', plain,
% 6.36/6.58      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 6.36/6.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.36/6.58  thf(redefinition_r2_relset_1, axiom,
% 6.36/6.58    (![A:$i,B:$i,C:$i,D:$i]:
% 6.36/6.58     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.36/6.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.36/6.58       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 6.36/6.58  thf('40', plain,
% 6.36/6.58      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 6.36/6.58         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 6.36/6.58          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 6.36/6.58          | (r2_relset_1 @ X29 @ X30 @ X28 @ X31)
% 6.36/6.58          | ((X28) != (X31)))),
% 6.36/6.58      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 6.36/6.58  thf('41', plain,
% 6.36/6.58      (![X29 : $i, X30 : $i, X31 : $i]:
% 6.36/6.58         ((r2_relset_1 @ X29 @ X30 @ X31 @ X31)
% 6.36/6.58          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 6.36/6.58      inference('simplify', [status(thm)], ['40'])).
% 6.36/6.58  thf('42', plain,
% 6.36/6.58      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 6.36/6.58      inference('sup-', [status(thm)], ['39', '41'])).
% 6.36/6.58  thf('43', plain,
% 6.36/6.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.36/6.58         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 6.36/6.58      inference('sup+', [status(thm)], ['38', '42'])).
% 6.36/6.58  thf('44', plain,
% 6.36/6.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.36/6.58         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 6.36/6.58          | ~ (v1_xboole_0 @ X0)
% 6.36/6.58          | ~ (v1_xboole_0 @ X1))),
% 6.36/6.58      inference('sup+', [status(thm)], ['37', '43'])).
% 6.36/6.58  thf('45', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 6.36/6.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.36/6.58  thf('46', plain, ((~ (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 6.36/6.58      inference('sup-', [status(thm)], ['44', '45'])).
% 6.36/6.58  thf('47', plain,
% 6.36/6.58      (![X0 : $i]:
% 6.36/6.58         (~ (v1_xboole_0 @ X0)
% 6.36/6.58          | ~ (v1_xboole_0 @ X0)
% 6.36/6.58          | ((sk_A) = (k1_relat_1 @ sk_D))
% 6.36/6.58          | ~ (v1_xboole_0 @ sk_D))),
% 6.36/6.58      inference('sup-', [status(thm)], ['32', '46'])).
% 6.36/6.58  thf('48', plain,
% 6.36/6.58      (![X0 : $i]:
% 6.36/6.58         (~ (v1_xboole_0 @ sk_D)
% 6.36/6.58          | ((sk_A) = (k1_relat_1 @ sk_D))
% 6.36/6.58          | ~ (v1_xboole_0 @ X0))),
% 6.36/6.58      inference('simplify', [status(thm)], ['47'])).
% 6.36/6.58  thf('49', plain, ((~ (v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.36/6.58      inference('condensation', [status(thm)], ['48'])).
% 6.36/6.58  thf('50', plain,
% 6.36/6.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.36/6.58         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 6.36/6.58      inference('sup+', [status(thm)], ['1', '3'])).
% 6.36/6.58  thf('51', plain,
% 6.36/6.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 6.36/6.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.36/6.58  thf('52', plain,
% 6.36/6.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.36/6.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.36/6.58  thf('53', plain,
% 6.36/6.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 6.36/6.58         (~ (r2_hidden @ X13 @ X14)
% 6.36/6.58          | (r2_hidden @ X13 @ X15)
% 6.36/6.58          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 6.36/6.58      inference('cnf', [status(esa)], [l3_subset_1])).
% 6.36/6.58  thf('54', plain,
% 6.36/6.58      (![X0 : $i]:
% 6.36/6.58         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 6.36/6.58          | ~ (r2_hidden @ X0 @ sk_D))),
% 6.36/6.58      inference('sup-', [status(thm)], ['52', '53'])).
% 6.36/6.58  thf('55', plain,
% 6.36/6.58      (((v1_xboole_0 @ sk_D)
% 6.36/6.58        | (r2_hidden @ (sk_B @ sk_D) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.36/6.58      inference('sup-', [status(thm)], ['51', '54'])).
% 6.36/6.58  thf('56', plain,
% 6.36/6.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.36/6.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.36/6.58  thf('57', plain,
% 6.36/6.58      (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.36/6.58      inference('sup-', [status(thm)], ['55', '56'])).
% 6.36/6.58  thf('58', plain,
% 6.36/6.58      (![X0 : $i]:
% 6.36/6.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 6.36/6.58          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 6.36/6.58          | (v1_xboole_0 @ sk_D))),
% 6.36/6.58      inference('sup-', [status(thm)], ['50', '57'])).
% 6.36/6.58  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.36/6.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.36/6.58  thf('60', plain,
% 6.36/6.58      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 6.36/6.58      inference('demod', [status(thm)], ['58', '59'])).
% 6.36/6.58  thf('61', plain,
% 6.36/6.58      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 6.36/6.58        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 6.36/6.58      inference('sup-', [status(thm)], ['15', '16'])).
% 6.36/6.58  thf('62', plain,
% 6.36/6.58      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 6.36/6.58      inference('sup-', [status(thm)], ['60', '61'])).
% 6.36/6.58  thf('63', plain,
% 6.36/6.58      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 6.36/6.58        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.36/6.58      inference('demod', [status(thm)], ['21', '24'])).
% 6.36/6.58  thf('64', plain, (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 6.36/6.58      inference('sup-', [status(thm)], ['62', '63'])).
% 6.36/6.58  thf('65', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 6.36/6.58      inference('clc', [status(thm)], ['49', '64'])).
% 6.36/6.58  thf('66', plain,
% 6.36/6.58      (![X0 : $i, X1 : $i]:
% 6.36/6.58         ((zip_tseitin_0 @ sk_B_1 @ X1) | (r1_tarski @ sk_C_2 @ X0))),
% 6.36/6.58      inference('demod', [status(thm)], ['12', '13'])).
% 6.36/6.58  thf('67', plain,
% 6.36/6.58      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.36/6.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.36/6.58  thf('68', plain,
% 6.36/6.58      (![X37 : $i, X38 : $i, X39 : $i]:
% 6.36/6.58         (~ (zip_tseitin_0 @ X37 @ X38)
% 6.36/6.58          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 6.36/6.58          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 6.36/6.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.36/6.58  thf('69', plain,
% 6.36/6.58      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 6.36/6.58        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 6.36/6.58      inference('sup-', [status(thm)], ['67', '68'])).
% 6.36/6.58  thf('70', plain,
% 6.36/6.58      (![X0 : $i]:
% 6.36/6.58         ((r1_tarski @ sk_C_2 @ X0) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 6.36/6.58      inference('sup-', [status(thm)], ['66', '69'])).
% 6.36/6.58  thf('71', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 6.36/6.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.36/6.58  thf('72', plain,
% 6.36/6.58      (![X34 : $i, X35 : $i, X36 : $i]:
% 6.36/6.58         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 6.36/6.58          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 6.36/6.58          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 6.36/6.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.36/6.58  thf('73', plain,
% 6.36/6.58      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 6.36/6.58        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 6.36/6.58      inference('sup-', [status(thm)], ['71', '72'])).
% 6.36/6.58  thf('74', plain,
% 6.36/6.58      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.36/6.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.36/6.58  thf('75', plain,
% 6.36/6.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.36/6.58         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 6.36/6.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 6.36/6.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.36/6.58  thf('76', plain,
% 6.36/6.58      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 6.36/6.58      inference('sup-', [status(thm)], ['74', '75'])).
% 6.36/6.58  thf('77', plain,
% 6.36/6.58      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 6.36/6.58        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 6.36/6.58      inference('demod', [status(thm)], ['73', '76'])).
% 6.36/6.58  thf('78', plain,
% 6.36/6.58      (![X0 : $i]:
% 6.36/6.58         ((r1_tarski @ sk_C_2 @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 6.36/6.58      inference('sup-', [status(thm)], ['70', '77'])).
% 6.36/6.58  thf('79', plain,
% 6.36/6.58      (![X0 : $i, X1 : $i]:
% 6.36/6.58         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 6.36/6.58      inference('sup-', [status(thm)], ['29', '30'])).
% 6.36/6.58  thf('80', plain,
% 6.36/6.58      (![X0 : $i]:
% 6.36/6.58         (((sk_A) = (k1_relat_1 @ sk_C_2))
% 6.36/6.58          | ((sk_C_2) = (X0))
% 6.36/6.58          | ~ (v1_xboole_0 @ X0))),
% 6.36/6.58      inference('sup-', [status(thm)], ['78', '79'])).
% 6.36/6.58  thf('81', plain, ((~ (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 6.36/6.58      inference('sup-', [status(thm)], ['44', '45'])).
% 6.36/6.58  thf('82', plain,
% 6.36/6.58      (![X0 : $i]:
% 6.36/6.58         (~ (v1_xboole_0 @ X0)
% 6.36/6.58          | ~ (v1_xboole_0 @ X0)
% 6.36/6.58          | ((sk_A) = (k1_relat_1 @ sk_C_2))
% 6.36/6.58          | ~ (v1_xboole_0 @ sk_D))),
% 6.36/6.58      inference('sup-', [status(thm)], ['80', '81'])).
% 6.36/6.58  thf('83', plain,
% 6.36/6.58      (![X0 : $i]:
% 6.36/6.58         (~ (v1_xboole_0 @ sk_D)
% 6.36/6.58          | ((sk_A) = (k1_relat_1 @ sk_C_2))
% 6.36/6.58          | ~ (v1_xboole_0 @ X0))),
% 6.36/6.58      inference('simplify', [status(thm)], ['82'])).
% 6.36/6.58  thf('84', plain,
% 6.36/6.58      ((~ (v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 6.36/6.58      inference('condensation', [status(thm)], ['83'])).
% 6.36/6.58  thf('85', plain,
% 6.36/6.58      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 6.36/6.58      inference('demod', [status(thm)], ['58', '59'])).
% 6.36/6.58  thf('86', plain,
% 6.36/6.58      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 6.36/6.58        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 6.36/6.58      inference('sup-', [status(thm)], ['67', '68'])).
% 6.36/6.58  thf('87', plain,
% 6.36/6.58      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 6.36/6.58      inference('sup-', [status(thm)], ['85', '86'])).
% 6.36/6.58  thf('88', plain,
% 6.36/6.58      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 6.36/6.58        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 6.36/6.58      inference('demod', [status(thm)], ['73', '76'])).
% 6.36/6.58  thf('89', plain, (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 6.36/6.58      inference('sup-', [status(thm)], ['87', '88'])).
% 6.36/6.58  thf('90', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 6.36/6.58      inference('clc', [status(thm)], ['84', '89'])).
% 6.36/6.58  thf(t9_funct_1, axiom,
% 6.36/6.58    (![A:$i]:
% 6.36/6.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.36/6.58       ( ![B:$i]:
% 6.36/6.58         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.36/6.58           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 6.36/6.58               ( ![C:$i]:
% 6.36/6.58                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 6.36/6.58                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 6.36/6.58             ( ( A ) = ( B ) ) ) ) ) ))).
% 6.36/6.58  thf('91', plain,
% 6.36/6.58      (![X20 : $i, X21 : $i]:
% 6.36/6.58         (~ (v1_relat_1 @ X20)
% 6.36/6.58          | ~ (v1_funct_1 @ X20)
% 6.36/6.58          | ((X21) = (X20))
% 6.36/6.58          | (r2_hidden @ (sk_C_1 @ X20 @ X21) @ (k1_relat_1 @ X21))
% 6.36/6.58          | ((k1_relat_1 @ X21) != (k1_relat_1 @ X20))
% 6.36/6.58          | ~ (v1_funct_1 @ X21)
% 6.36/6.58          | ~ (v1_relat_1 @ X21))),
% 6.36/6.58      inference('cnf', [status(esa)], [t9_funct_1])).
% 6.36/6.58  thf('92', plain,
% 6.36/6.58      (![X0 : $i]:
% 6.36/6.58         (((sk_A) != (k1_relat_1 @ X0))
% 6.36/6.58          | ~ (v1_relat_1 @ sk_C_2)
% 6.36/6.58          | ~ (v1_funct_1 @ sk_C_2)
% 6.36/6.58          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 6.36/6.58          | ((sk_C_2) = (X0))
% 6.36/6.58          | ~ (v1_funct_1 @ X0)
% 6.36/6.58          | ~ (v1_relat_1 @ X0))),
% 6.36/6.58      inference('sup-', [status(thm)], ['90', '91'])).
% 6.36/6.58  thf('93', plain,
% 6.36/6.58      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.36/6.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.36/6.58  thf(cc1_relset_1, axiom,
% 6.36/6.58    (![A:$i,B:$i,C:$i]:
% 6.36/6.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.36/6.58       ( v1_relat_1 @ C ) ))).
% 6.36/6.58  thf('94', plain,
% 6.36/6.58      (![X22 : $i, X23 : $i, X24 : $i]:
% 6.36/6.58         ((v1_relat_1 @ X22)
% 6.36/6.58          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 6.36/6.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.36/6.58  thf('95', plain, ((v1_relat_1 @ sk_C_2)),
% 6.36/6.58      inference('sup-', [status(thm)], ['93', '94'])).
% 6.36/6.58  thf('96', plain, ((v1_funct_1 @ sk_C_2)),
% 6.36/6.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.36/6.58  thf('97', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 6.36/6.58      inference('clc', [status(thm)], ['84', '89'])).
% 6.36/6.58  thf('98', plain,
% 6.36/6.58      (![X0 : $i]:
% 6.36/6.58         (((sk_A) != (k1_relat_1 @ X0))
% 6.36/6.58          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 6.36/6.58          | ((sk_C_2) = (X0))
% 6.36/6.58          | ~ (v1_funct_1 @ X0)
% 6.36/6.58          | ~ (v1_relat_1 @ X0))),
% 6.36/6.58      inference('demod', [status(thm)], ['92', '95', '96', '97'])).
% 6.36/6.58  thf('99', plain,
% 6.36/6.58      ((((sk_A) != (sk_A))
% 6.36/6.58        | ~ (v1_relat_1 @ sk_D)
% 6.36/6.58        | ~ (v1_funct_1 @ sk_D)
% 6.36/6.58        | ((sk_C_2) = (sk_D))
% 6.36/6.58        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 6.36/6.58      inference('sup-', [status(thm)], ['65', '98'])).
% 6.36/6.58  thf('100', plain,
% 6.36/6.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.36/6.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.36/6.58  thf('101', plain,
% 6.36/6.58      (![X22 : $i, X23 : $i, X24 : $i]:
% 6.36/6.58         ((v1_relat_1 @ X22)
% 6.36/6.58          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 6.36/6.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.36/6.58  thf('102', plain, ((v1_relat_1 @ sk_D)),
% 6.36/6.58      inference('sup-', [status(thm)], ['100', '101'])).
% 6.36/6.58  thf('103', plain, ((v1_funct_1 @ sk_D)),
% 6.36/6.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.36/6.58  thf('104', plain,
% 6.36/6.58      ((((sk_A) != (sk_A))
% 6.36/6.58        | ((sk_C_2) = (sk_D))
% 6.36/6.58        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 6.36/6.58      inference('demod', [status(thm)], ['99', '102', '103'])).
% 6.36/6.58  thf('105', plain,
% 6.36/6.58      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 6.36/6.58      inference('simplify', [status(thm)], ['104'])).
% 6.36/6.58  thf('106', plain,
% 6.36/6.58      (![X40 : $i]:
% 6.36/6.58         (((k1_funct_1 @ sk_C_2 @ X40) = (k1_funct_1 @ sk_D @ X40))
% 6.36/6.58          | ~ (r2_hidden @ X40 @ sk_A))),
% 6.36/6.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.36/6.58  thf('107', plain,
% 6.36/6.58      ((((sk_C_2) = (sk_D))
% 6.36/6.58        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 6.36/6.58            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 6.36/6.58      inference('sup-', [status(thm)], ['105', '106'])).
% 6.36/6.58  thf('108', plain,
% 6.36/6.58      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 6.36/6.58         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 6.36/6.58      inference('condensation', [status(thm)], ['107'])).
% 6.36/6.58  thf('109', plain,
% 6.36/6.58      (![X20 : $i, X21 : $i]:
% 6.36/6.58         (~ (v1_relat_1 @ X20)
% 6.36/6.58          | ~ (v1_funct_1 @ X20)
% 6.36/6.58          | ((X21) = (X20))
% 6.36/6.58          | ((k1_funct_1 @ X21 @ (sk_C_1 @ X20 @ X21))
% 6.36/6.58              != (k1_funct_1 @ X20 @ (sk_C_1 @ X20 @ X21)))
% 6.36/6.58          | ((k1_relat_1 @ X21) != (k1_relat_1 @ X20))
% 6.36/6.58          | ~ (v1_funct_1 @ X21)
% 6.36/6.58          | ~ (v1_relat_1 @ X21))),
% 6.36/6.58      inference('cnf', [status(esa)], [t9_funct_1])).
% 6.36/6.58  thf('110', plain,
% 6.36/6.58      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 6.36/6.58          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 6.36/6.58        | ~ (v1_relat_1 @ sk_C_2)
% 6.36/6.58        | ~ (v1_funct_1 @ sk_C_2)
% 6.36/6.58        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 6.36/6.58        | ((sk_C_2) = (sk_D))
% 6.36/6.58        | ~ (v1_funct_1 @ sk_D)
% 6.36/6.58        | ~ (v1_relat_1 @ sk_D))),
% 6.36/6.58      inference('sup-', [status(thm)], ['108', '109'])).
% 6.36/6.58  thf('111', plain, ((v1_relat_1 @ sk_C_2)),
% 6.36/6.58      inference('sup-', [status(thm)], ['93', '94'])).
% 6.36/6.58  thf('112', plain, ((v1_funct_1 @ sk_C_2)),
% 6.36/6.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.36/6.58  thf('113', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 6.36/6.58      inference('clc', [status(thm)], ['84', '89'])).
% 6.36/6.58  thf('114', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 6.36/6.58      inference('clc', [status(thm)], ['49', '64'])).
% 6.36/6.58  thf('115', plain, ((v1_funct_1 @ sk_D)),
% 6.36/6.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.36/6.58  thf('116', plain, ((v1_relat_1 @ sk_D)),
% 6.36/6.58      inference('sup-', [status(thm)], ['100', '101'])).
% 6.36/6.58  thf('117', plain,
% 6.36/6.58      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 6.36/6.58          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 6.36/6.58        | ((sk_A) != (sk_A))
% 6.36/6.58        | ((sk_C_2) = (sk_D)))),
% 6.36/6.58      inference('demod', [status(thm)],
% 6.36/6.58                ['110', '111', '112', '113', '114', '115', '116'])).
% 6.36/6.58  thf('118', plain, (((sk_C_2) = (sk_D))),
% 6.36/6.58      inference('simplify', [status(thm)], ['117'])).
% 6.36/6.58  thf('119', plain,
% 6.36/6.58      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.36/6.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.36/6.58  thf('120', plain,
% 6.36/6.58      (![X29 : $i, X30 : $i, X31 : $i]:
% 6.36/6.58         ((r2_relset_1 @ X29 @ X30 @ X31 @ X31)
% 6.36/6.58          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 6.36/6.58      inference('simplify', [status(thm)], ['40'])).
% 6.36/6.58  thf('121', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 6.36/6.58      inference('sup-', [status(thm)], ['119', '120'])).
% 6.36/6.58  thf('122', plain, ($false),
% 6.36/6.58      inference('demod', [status(thm)], ['0', '118', '121'])).
% 6.36/6.58  
% 6.36/6.58  % SZS output end Refutation
% 6.36/6.58  
% 6.36/6.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

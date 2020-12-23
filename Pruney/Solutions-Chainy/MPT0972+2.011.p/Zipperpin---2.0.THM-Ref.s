%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7DdfKLbTlC

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:34 EST 2020

% Result     : Theorem 15.59s
% Output     : Refutation 15.59s
% Verified   : 
% Statistics : Number of formulae       :  224 (3124 expanded)
%              Number of leaves         :   39 ( 922 expanded)
%              Depth                    :   46
%              Number of atoms          : 1861 (51891 expanded)
%              Number of equality atoms :  203 (2798 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('4',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('11',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('15',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('18',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('22',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('25',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

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

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X15 = X14 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ( ( k1_relat_1 @ X15 )
       != ( k1_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('32',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','32','33'])).

thf('35',plain,
    ( ( sk_A != sk_A )
    | ( sk_B_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('38',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_A != sk_A )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','38','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2 = sk_D )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('43',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('44',plain,(
    v4_relat_1 @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('48',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ),
    inference(demod,[status(thm)],['46','47'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,(
    ! [X37: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X37 )
        = ( k1_funct_1 @ sk_D @ X37 ) )
      | ~ ( r2_hidden @ X37 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( sk_C_2 = sk_D )
    | ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['53'])).

thf('55',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X15 = X14 )
      | ( ( k1_funct_1 @ X15 @ ( sk_C_1 @ X14 @ X15 ) )
       != ( k1_funct_1 @ X14 @ ( sk_C_1 @ X14 @ X15 ) ) )
      | ( ( k1_relat_1 @ X15 )
       != ( k1_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('56',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('58',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('61',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['56','57','58','59','60'])).

thf('62',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != sk_A )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference('sup-',[status(thm)],['13','62'])).

thf('64',plain,
    ( ( sk_C_2 = sk_D )
    | ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != sk_A ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('66',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('70',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['70'])).

thf('72',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['68','72'])).

thf('74',plain,(
    ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['0','73'])).

thf('75',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('76',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('77',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['75','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('82',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ( v4_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('89',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('90',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('94',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('96',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['68','72'])).

thf('99',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('100',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('102',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ sk_C_2 @ X0 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('106',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ X0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('108',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('111',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('112',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('114',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_fact,[status(thm)],['114'])).

thf('116',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['109','115'])).

thf('117',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['106','107'])).

thf('118',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X15 = X14 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ( ( k1_relat_1 @ X15 )
       != ( k1_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('121',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['106','107'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ k1_xboole_0 )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120','121','122'])).

thf('124',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['116','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('126',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 = sk_D )
      | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','131'])).

thf('133',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['106','107'])).

thf('134',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('135',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X15 = X14 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ( ( k1_relat_1 @ X15 )
       != ( k1_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_relat_1 @ X0 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_D ) @ ( k1_relat_1 @ sk_D ) )
      | ( sk_D = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('138',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_relat_1 @ X0 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_D ) @ ( k1_relat_1 @ sk_D ) )
      | ( sk_D = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['106','107'])).

thf('141',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['109','115'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_relat_1 @ X0 ) )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_D ) @ k1_xboole_0 )
      | ( sk_D = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( sk_D = sk_C_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_D ) @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['133','142'])).

thf('144',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('145',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = sk_C_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_D ) @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_D ) @ k1_xboole_0 )
    | ( sk_D = sk_C_2 ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( sk_D = sk_C_2 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X37: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X37 )
        = ( k1_funct_1 @ sk_D @ X37 ) )
      | ~ ( r2_hidden @ X37 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D = sk_C_2 )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_D ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_D ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_C_2 @ sk_D ) ) ) ),
    inference(condensation,[status(thm)],['151'])).

thf('153',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X15 = X14 )
      | ( ( k1_funct_1 @ X15 @ ( sk_C_1 @ X14 @ X15 ) )
       != ( k1_funct_1 @ X14 @ ( sk_C_1 @ X14 @ X15 ) ) )
      | ( ( k1_relat_1 @ X15 )
       != ( k1_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('154',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_D ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_D ) ) )
    | ( sk_A = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
     != ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_D = sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('156',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['109','115'])).

thf('158',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['106','107'])).

thf('159',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('161',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_D ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_D ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = sk_C_2 ) ),
    inference(demod,[status(thm)],['154','155','156','157','158','159','160'])).

thf('162',plain,
    ( ( sk_D = sk_C_2 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X37: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X37 )
        = ( k1_funct_1 @ sk_D @ X37 ) )
      | ~ ( r2_hidden @ X37 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( sk_D = sk_C_2 )
      | ( ( k1_funct_1 @ sk_C_2 @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ sk_C_2 @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) ) ) ),
    inference(condensation,[status(thm)],['164'])).

thf('166',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['132','165'])).

thf('167',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['166'])).

thf('168',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X15 = X14 )
      | ( ( k1_funct_1 @ X15 @ ( sk_C_1 @ X14 @ X15 ) )
       != ( k1_funct_1 @ X14 @ ( sk_C_1 @ X14 @ X15 ) ) )
      | ( ( k1_relat_1 @ X15 )
       != ( k1_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('169',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('171',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['106','107'])).

thf('173',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['109','115'])).

thf('174',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('176',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['169','170','171','172','173','174','175'])).

thf('177',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('179',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('180',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['70'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( r2_relset_1 @ X0 @ k1_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ k1_xboole_0 @ sk_C_2 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['178','181'])).

thf('183',plain,(
    $false ),
    inference(demod,[status(thm)],['74','177','182'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7DdfKLbTlC
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:47:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 15.59/15.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 15.59/15.81  % Solved by: fo/fo7.sh
% 15.59/15.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.59/15.81  % done 11441 iterations in 15.353s
% 15.59/15.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 15.59/15.81  % SZS output start Refutation
% 15.59/15.81  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 15.59/15.81  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 15.59/15.81  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 15.59/15.81  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 15.59/15.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 15.59/15.81  thf(sk_D_type, type, sk_D: $i).
% 15.59/15.81  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 15.59/15.81  thf(sk_A_type, type, sk_A: $i).
% 15.59/15.81  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 15.59/15.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 15.59/15.81  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 15.59/15.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 15.59/15.81  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 15.59/15.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 15.59/15.81  thf(sk_B_1_type, type, sk_B_1: $i).
% 15.59/15.81  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 15.59/15.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 15.59/15.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 15.59/15.81  thf(sk_C_2_type, type, sk_C_2: $i).
% 15.59/15.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 15.59/15.81  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 15.59/15.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 15.59/15.81  thf(t18_funct_2, conjecture,
% 15.59/15.81    (![A:$i,B:$i,C:$i]:
% 15.59/15.81     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 15.59/15.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.59/15.81       ( ![D:$i]:
% 15.59/15.81         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 15.59/15.81             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.59/15.81           ( ( ![E:$i]:
% 15.59/15.81               ( ( r2_hidden @ E @ A ) =>
% 15.59/15.81                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 15.59/15.81             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 15.59/15.81  thf(zf_stmt_0, negated_conjecture,
% 15.59/15.81    (~( ![A:$i,B:$i,C:$i]:
% 15.59/15.81        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 15.59/15.81            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.59/15.81          ( ![D:$i]:
% 15.59/15.81            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 15.59/15.81                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.59/15.81              ( ( ![E:$i]:
% 15.59/15.81                  ( ( r2_hidden @ E @ A ) =>
% 15.59/15.81                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 15.59/15.81                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 15.59/15.81    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 15.59/15.81  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf(d1_funct_2, axiom,
% 15.59/15.81    (![A:$i,B:$i,C:$i]:
% 15.59/15.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.59/15.81       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 15.59/15.81           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 15.59/15.81             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 15.59/15.81         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.59/15.81           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 15.59/15.81             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 15.59/15.81  thf(zf_stmt_1, axiom,
% 15.59/15.81    (![B:$i,A:$i]:
% 15.59/15.81     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.59/15.81       ( zip_tseitin_0 @ B @ A ) ))).
% 15.59/15.81  thf('1', plain,
% 15.59/15.81      (![X29 : $i, X30 : $i]:
% 15.59/15.81         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.59/15.81  thf('2', plain,
% 15.59/15.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 15.59/15.81  thf(zf_stmt_3, axiom,
% 15.59/15.81    (![C:$i,B:$i,A:$i]:
% 15.59/15.81     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 15.59/15.81       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 15.59/15.81  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 15.59/15.81  thf(zf_stmt_5, axiom,
% 15.59/15.81    (![A:$i,B:$i,C:$i]:
% 15.59/15.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.59/15.81       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 15.59/15.81         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 15.59/15.81           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 15.59/15.81             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 15.59/15.81  thf('3', plain,
% 15.59/15.81      (![X34 : $i, X35 : $i, X36 : $i]:
% 15.59/15.81         (~ (zip_tseitin_0 @ X34 @ X35)
% 15.59/15.81          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 15.59/15.81          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_5])).
% 15.59/15.81  thf('4', plain,
% 15.59/15.81      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 15.59/15.81        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 15.59/15.81      inference('sup-', [status(thm)], ['2', '3'])).
% 15.59/15.81  thf('5', plain,
% 15.59/15.81      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 15.59/15.81      inference('sup-', [status(thm)], ['1', '4'])).
% 15.59/15.81  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('7', plain,
% 15.59/15.81      (![X31 : $i, X32 : $i, X33 : $i]:
% 15.59/15.81         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 15.59/15.81          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 15.59/15.81          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 15.59/15.81  thf('8', plain,
% 15.59/15.81      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 15.59/15.81        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 15.59/15.81      inference('sup-', [status(thm)], ['6', '7'])).
% 15.59/15.81  thf('9', plain,
% 15.59/15.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf(redefinition_k1_relset_1, axiom,
% 15.59/15.81    (![A:$i,B:$i,C:$i]:
% 15.59/15.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.59/15.81       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 15.59/15.81  thf('10', plain,
% 15.59/15.81      (![X22 : $i, X23 : $i, X24 : $i]:
% 15.59/15.81         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 15.59/15.81          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 15.59/15.81      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 15.59/15.81  thf('11', plain,
% 15.59/15.81      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 15.59/15.81      inference('sup-', [status(thm)], ['9', '10'])).
% 15.59/15.81  thf('12', plain,
% 15.59/15.81      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 15.59/15.81        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.59/15.81      inference('demod', [status(thm)], ['8', '11'])).
% 15.59/15.81  thf('13', plain,
% 15.59/15.81      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.59/15.81      inference('sup-', [status(thm)], ['5', '12'])).
% 15.59/15.81  thf('14', plain,
% 15.59/15.81      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.59/15.81      inference('sup-', [status(thm)], ['5', '12'])).
% 15.59/15.81  thf('15', plain,
% 15.59/15.81      (![X29 : $i, X30 : $i]:
% 15.59/15.81         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.59/15.81  thf('16', plain,
% 15.59/15.81      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('17', plain,
% 15.59/15.81      (![X34 : $i, X35 : $i, X36 : $i]:
% 15.59/15.81         (~ (zip_tseitin_0 @ X34 @ X35)
% 15.59/15.81          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 15.59/15.81          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_5])).
% 15.59/15.81  thf('18', plain,
% 15.59/15.81      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 15.59/15.81        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 15.59/15.81      inference('sup-', [status(thm)], ['16', '17'])).
% 15.59/15.81  thf('19', plain,
% 15.59/15.81      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 15.59/15.81      inference('sup-', [status(thm)], ['15', '18'])).
% 15.59/15.81  thf('20', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('21', plain,
% 15.59/15.81      (![X31 : $i, X32 : $i, X33 : $i]:
% 15.59/15.81         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 15.59/15.81          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 15.59/15.81          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 15.59/15.81  thf('22', plain,
% 15.59/15.81      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 15.59/15.81        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 15.59/15.81      inference('sup-', [status(thm)], ['20', '21'])).
% 15.59/15.81  thf('23', plain,
% 15.59/15.81      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('24', plain,
% 15.59/15.81      (![X22 : $i, X23 : $i, X24 : $i]:
% 15.59/15.81         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 15.59/15.81          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 15.59/15.81      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 15.59/15.81  thf('25', plain,
% 15.59/15.81      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 15.59/15.81      inference('sup-', [status(thm)], ['23', '24'])).
% 15.59/15.81  thf('26', plain,
% 15.59/15.81      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 15.59/15.81        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 15.59/15.81      inference('demod', [status(thm)], ['22', '25'])).
% 15.59/15.81  thf('27', plain,
% 15.59/15.81      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 15.59/15.81      inference('sup-', [status(thm)], ['19', '26'])).
% 15.59/15.81  thf(t9_funct_1, axiom,
% 15.59/15.81    (![A:$i]:
% 15.59/15.81     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 15.59/15.81       ( ![B:$i]:
% 15.59/15.81         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 15.59/15.81           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 15.59/15.81               ( ![C:$i]:
% 15.59/15.81                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 15.59/15.81                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 15.59/15.81             ( ( A ) = ( B ) ) ) ) ) ))).
% 15.59/15.81  thf('28', plain,
% 15.59/15.81      (![X14 : $i, X15 : $i]:
% 15.59/15.81         (~ (v1_relat_1 @ X14)
% 15.59/15.81          | ~ (v1_funct_1 @ X14)
% 15.59/15.81          | ((X15) = (X14))
% 15.59/15.81          | (r2_hidden @ (sk_C_1 @ X14 @ X15) @ (k1_relat_1 @ X15))
% 15.59/15.81          | ((k1_relat_1 @ X15) != (k1_relat_1 @ X14))
% 15.59/15.81          | ~ (v1_funct_1 @ X15)
% 15.59/15.81          | ~ (v1_relat_1 @ X15))),
% 15.59/15.81      inference('cnf', [status(esa)], [t9_funct_1])).
% 15.59/15.81  thf('29', plain,
% 15.59/15.81      (![X0 : $i]:
% 15.59/15.81         (((sk_A) != (k1_relat_1 @ X0))
% 15.59/15.81          | ((sk_B_1) = (k1_xboole_0))
% 15.59/15.81          | ~ (v1_relat_1 @ sk_C_2)
% 15.59/15.81          | ~ (v1_funct_1 @ sk_C_2)
% 15.59/15.81          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 15.59/15.81          | ((sk_C_2) = (X0))
% 15.59/15.81          | ~ (v1_funct_1 @ X0)
% 15.59/15.81          | ~ (v1_relat_1 @ X0))),
% 15.59/15.81      inference('sup-', [status(thm)], ['27', '28'])).
% 15.59/15.81  thf('30', plain,
% 15.59/15.81      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf(cc1_relset_1, axiom,
% 15.59/15.81    (![A:$i,B:$i,C:$i]:
% 15.59/15.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.59/15.81       ( v1_relat_1 @ C ) ))).
% 15.59/15.81  thf('31', plain,
% 15.59/15.81      (![X16 : $i, X17 : $i, X18 : $i]:
% 15.59/15.81         ((v1_relat_1 @ X16)
% 15.59/15.81          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 15.59/15.81      inference('cnf', [status(esa)], [cc1_relset_1])).
% 15.59/15.81  thf('32', plain, ((v1_relat_1 @ sk_C_2)),
% 15.59/15.81      inference('sup-', [status(thm)], ['30', '31'])).
% 15.59/15.81  thf('33', plain, ((v1_funct_1 @ sk_C_2)),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('34', plain,
% 15.59/15.81      (![X0 : $i]:
% 15.59/15.81         (((sk_A) != (k1_relat_1 @ X0))
% 15.59/15.81          | ((sk_B_1) = (k1_xboole_0))
% 15.59/15.81          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 15.59/15.81          | ((sk_C_2) = (X0))
% 15.59/15.81          | ~ (v1_funct_1 @ X0)
% 15.59/15.81          | ~ (v1_relat_1 @ X0))),
% 15.59/15.81      inference('demod', [status(thm)], ['29', '32', '33'])).
% 15.59/15.81  thf('35', plain,
% 15.59/15.81      ((((sk_A) != (sk_A))
% 15.59/15.81        | ((sk_B_1) = (k1_xboole_0))
% 15.59/15.81        | ~ (v1_relat_1 @ sk_D)
% 15.59/15.81        | ~ (v1_funct_1 @ sk_D)
% 15.59/15.81        | ((sk_C_2) = (sk_D))
% 15.59/15.81        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 15.59/15.81        | ((sk_B_1) = (k1_xboole_0)))),
% 15.59/15.81      inference('sup-', [status(thm)], ['14', '34'])).
% 15.59/15.81  thf('36', plain,
% 15.59/15.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('37', plain,
% 15.59/15.81      (![X16 : $i, X17 : $i, X18 : $i]:
% 15.59/15.81         ((v1_relat_1 @ X16)
% 15.59/15.81          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 15.59/15.81      inference('cnf', [status(esa)], [cc1_relset_1])).
% 15.59/15.81  thf('38', plain, ((v1_relat_1 @ sk_D)),
% 15.59/15.81      inference('sup-', [status(thm)], ['36', '37'])).
% 15.59/15.81  thf('39', plain, ((v1_funct_1 @ sk_D)),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('40', plain,
% 15.59/15.81      ((((sk_A) != (sk_A))
% 15.59/15.81        | ((sk_B_1) = (k1_xboole_0))
% 15.59/15.81        | ((sk_C_2) = (sk_D))
% 15.59/15.81        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 15.59/15.81        | ((sk_B_1) = (k1_xboole_0)))),
% 15.59/15.81      inference('demod', [status(thm)], ['35', '38', '39'])).
% 15.59/15.81  thf('41', plain,
% 15.59/15.81      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 15.59/15.81        | ((sk_C_2) = (sk_D))
% 15.59/15.81        | ((sk_B_1) = (k1_xboole_0)))),
% 15.59/15.81      inference('simplify', [status(thm)], ['40'])).
% 15.59/15.81  thf('42', plain,
% 15.59/15.81      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf(cc2_relset_1, axiom,
% 15.59/15.81    (![A:$i,B:$i,C:$i]:
% 15.59/15.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.59/15.81       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 15.59/15.81  thf('43', plain,
% 15.59/15.81      (![X19 : $i, X20 : $i, X21 : $i]:
% 15.59/15.81         ((v4_relat_1 @ X19 @ X20)
% 15.59/15.81          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 15.59/15.81      inference('cnf', [status(esa)], [cc2_relset_1])).
% 15.59/15.81  thf('44', plain, ((v4_relat_1 @ sk_C_2 @ sk_A)),
% 15.59/15.81      inference('sup-', [status(thm)], ['42', '43'])).
% 15.59/15.81  thf(d18_relat_1, axiom,
% 15.59/15.81    (![A:$i,B:$i]:
% 15.59/15.81     ( ( v1_relat_1 @ B ) =>
% 15.59/15.81       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 15.59/15.81  thf('45', plain,
% 15.59/15.81      (![X12 : $i, X13 : $i]:
% 15.59/15.81         (~ (v4_relat_1 @ X12 @ X13)
% 15.59/15.81          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 15.59/15.81          | ~ (v1_relat_1 @ X12))),
% 15.59/15.81      inference('cnf', [status(esa)], [d18_relat_1])).
% 15.59/15.81  thf('46', plain,
% 15.59/15.81      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_A))),
% 15.59/15.81      inference('sup-', [status(thm)], ['44', '45'])).
% 15.59/15.81  thf('47', plain, ((v1_relat_1 @ sk_C_2)),
% 15.59/15.81      inference('sup-', [status(thm)], ['30', '31'])).
% 15.59/15.81  thf('48', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_A)),
% 15.59/15.81      inference('demod', [status(thm)], ['46', '47'])).
% 15.59/15.81  thf(d3_tarski, axiom,
% 15.59/15.81    (![A:$i,B:$i]:
% 15.59/15.81     ( ( r1_tarski @ A @ B ) <=>
% 15.59/15.81       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 15.59/15.81  thf('49', plain,
% 15.59/15.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.59/15.81         (~ (r2_hidden @ X0 @ X1)
% 15.59/15.81          | (r2_hidden @ X0 @ X2)
% 15.59/15.81          | ~ (r1_tarski @ X1 @ X2))),
% 15.59/15.81      inference('cnf', [status(esa)], [d3_tarski])).
% 15.59/15.81  thf('50', plain,
% 15.59/15.81      (![X0 : $i]:
% 15.59/15.81         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2)))),
% 15.59/15.81      inference('sup-', [status(thm)], ['48', '49'])).
% 15.59/15.81  thf('51', plain,
% 15.59/15.81      ((((sk_B_1) = (k1_xboole_0))
% 15.59/15.81        | ((sk_C_2) = (sk_D))
% 15.59/15.81        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 15.59/15.81      inference('sup-', [status(thm)], ['41', '50'])).
% 15.59/15.81  thf('52', plain,
% 15.59/15.81      (![X37 : $i]:
% 15.59/15.81         (((k1_funct_1 @ sk_C_2 @ X37) = (k1_funct_1 @ sk_D @ X37))
% 15.59/15.81          | ~ (r2_hidden @ X37 @ sk_A))),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('53', plain,
% 15.59/15.81      ((((sk_C_2) = (sk_D))
% 15.59/15.81        | ((sk_B_1) = (k1_xboole_0))
% 15.59/15.81        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 15.59/15.81            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 15.59/15.81      inference('sup-', [status(thm)], ['51', '52'])).
% 15.59/15.81  thf('54', plain,
% 15.59/15.81      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 15.59/15.81          = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))
% 15.59/15.81        | ((sk_B_1) = (k1_xboole_0)))),
% 15.59/15.81      inference('condensation', [status(thm)], ['53'])).
% 15.59/15.81  thf('55', plain,
% 15.59/15.81      (![X14 : $i, X15 : $i]:
% 15.59/15.81         (~ (v1_relat_1 @ X14)
% 15.59/15.81          | ~ (v1_funct_1 @ X14)
% 15.59/15.81          | ((X15) = (X14))
% 15.59/15.81          | ((k1_funct_1 @ X15 @ (sk_C_1 @ X14 @ X15))
% 15.59/15.81              != (k1_funct_1 @ X14 @ (sk_C_1 @ X14 @ X15)))
% 15.59/15.81          | ((k1_relat_1 @ X15) != (k1_relat_1 @ X14))
% 15.59/15.81          | ~ (v1_funct_1 @ X15)
% 15.59/15.81          | ~ (v1_relat_1 @ X15))),
% 15.59/15.81      inference('cnf', [status(esa)], [t9_funct_1])).
% 15.59/15.81  thf('56', plain,
% 15.59/15.81      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 15.59/15.81          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 15.59/15.81        | ((sk_B_1) = (k1_xboole_0))
% 15.59/15.81        | ~ (v1_relat_1 @ sk_C_2)
% 15.59/15.81        | ~ (v1_funct_1 @ sk_C_2)
% 15.59/15.81        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 15.59/15.81        | ((sk_C_2) = (sk_D))
% 15.59/15.81        | ~ (v1_funct_1 @ sk_D)
% 15.59/15.81        | ~ (v1_relat_1 @ sk_D))),
% 15.59/15.81      inference('sup-', [status(thm)], ['54', '55'])).
% 15.59/15.81  thf('57', plain, ((v1_relat_1 @ sk_C_2)),
% 15.59/15.81      inference('sup-', [status(thm)], ['30', '31'])).
% 15.59/15.81  thf('58', plain, ((v1_funct_1 @ sk_C_2)),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('60', plain, ((v1_relat_1 @ sk_D)),
% 15.59/15.81      inference('sup-', [status(thm)], ['36', '37'])).
% 15.59/15.81  thf('61', plain,
% 15.59/15.81      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 15.59/15.81          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 15.59/15.81        | ((sk_B_1) = (k1_xboole_0))
% 15.59/15.81        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 15.59/15.81        | ((sk_C_2) = (sk_D)))),
% 15.59/15.81      inference('demod', [status(thm)], ['56', '57', '58', '59', '60'])).
% 15.59/15.81  thf('62', plain,
% 15.59/15.81      ((((sk_C_2) = (sk_D))
% 15.59/15.81        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 15.59/15.81        | ((sk_B_1) = (k1_xboole_0)))),
% 15.59/15.81      inference('simplify', [status(thm)], ['61'])).
% 15.59/15.81  thf('63', plain,
% 15.59/15.81      ((((k1_relat_1 @ sk_C_2) != (sk_A))
% 15.59/15.81        | ((sk_B_1) = (k1_xboole_0))
% 15.59/15.81        | ((sk_B_1) = (k1_xboole_0))
% 15.59/15.81        | ((sk_C_2) = (sk_D)))),
% 15.59/15.81      inference('sup-', [status(thm)], ['13', '62'])).
% 15.59/15.81  thf('64', plain,
% 15.59/15.81      ((((sk_C_2) = (sk_D))
% 15.59/15.81        | ((sk_B_1) = (k1_xboole_0))
% 15.59/15.81        | ((k1_relat_1 @ sk_C_2) != (sk_A)))),
% 15.59/15.81      inference('simplify', [status(thm)], ['63'])).
% 15.59/15.81  thf('65', plain,
% 15.59/15.81      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 15.59/15.81      inference('sup-', [status(thm)], ['19', '26'])).
% 15.59/15.81  thf('66', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_C_2) = (sk_D)))),
% 15.59/15.81      inference('clc', [status(thm)], ['64', '65'])).
% 15.59/15.81  thf('67', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('68', plain,
% 15.59/15.81      ((~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)
% 15.59/15.81        | ((sk_B_1) = (k1_xboole_0)))),
% 15.59/15.81      inference('sup-', [status(thm)], ['66', '67'])).
% 15.59/15.81  thf('69', plain,
% 15.59/15.81      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf(reflexivity_r2_relset_1, axiom,
% 15.59/15.81    (![A:$i,B:$i,C:$i,D:$i]:
% 15.59/15.81     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 15.59/15.81         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 15.59/15.81       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 15.59/15.81  thf('70', plain,
% 15.59/15.81      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 15.59/15.81         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 15.59/15.81          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 15.59/15.81          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 15.59/15.81      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 15.59/15.81  thf('71', plain,
% 15.59/15.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.59/15.81         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 15.59/15.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 15.59/15.81      inference('condensation', [status(thm)], ['70'])).
% 15.59/15.81  thf('72', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 15.59/15.81      inference('sup-', [status(thm)], ['69', '71'])).
% 15.59/15.81  thf('73', plain, (((sk_B_1) = (k1_xboole_0))),
% 15.59/15.81      inference('demod', [status(thm)], ['68', '72'])).
% 15.59/15.81  thf('74', plain, (~ (r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_2 @ sk_D)),
% 15.59/15.81      inference('demod', [status(thm)], ['0', '73'])).
% 15.59/15.81  thf('75', plain,
% 15.59/15.81      (![X29 : $i, X30 : $i]:
% 15.59/15.81         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.59/15.81  thf(t113_zfmisc_1, axiom,
% 15.59/15.81    (![A:$i,B:$i]:
% 15.59/15.81     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 15.59/15.81       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 15.59/15.81  thf('76', plain,
% 15.59/15.81      (![X9 : $i, X10 : $i]:
% 15.59/15.81         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 15.59/15.81      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 15.59/15.81  thf('77', plain,
% 15.59/15.81      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 15.59/15.81      inference('simplify', [status(thm)], ['76'])).
% 15.59/15.81  thf('78', plain,
% 15.59/15.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.59/15.81         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 15.59/15.81      inference('sup+', [status(thm)], ['75', '77'])).
% 15.59/15.81  thf('79', plain,
% 15.59/15.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('80', plain,
% 15.59/15.81      (![X0 : $i]:
% 15.59/15.81         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))
% 15.59/15.81          | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 15.59/15.81      inference('sup+', [status(thm)], ['78', '79'])).
% 15.59/15.81  thf('81', plain,
% 15.59/15.81      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 15.59/15.81      inference('simplify', [status(thm)], ['76'])).
% 15.59/15.81  thf('82', plain,
% 15.59/15.81      (![X19 : $i, X20 : $i, X21 : $i]:
% 15.59/15.81         ((v4_relat_1 @ X19 @ X20)
% 15.59/15.81          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 15.59/15.81      inference('cnf', [status(esa)], [cc2_relset_1])).
% 15.59/15.81  thf('83', plain,
% 15.59/15.81      (![X0 : $i, X1 : $i]:
% 15.59/15.81         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 15.59/15.81          | (v4_relat_1 @ X1 @ X0))),
% 15.59/15.81      inference('sup-', [status(thm)], ['81', '82'])).
% 15.59/15.81  thf('84', plain,
% 15.59/15.81      (![X0 : $i, X1 : $i]:
% 15.59/15.81         ((zip_tseitin_0 @ sk_B_1 @ X1) | (v4_relat_1 @ sk_D @ X0))),
% 15.59/15.81      inference('sup-', [status(thm)], ['80', '83'])).
% 15.59/15.81  thf('85', plain,
% 15.59/15.81      (![X12 : $i, X13 : $i]:
% 15.59/15.81         (~ (v4_relat_1 @ X12 @ X13)
% 15.59/15.81          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 15.59/15.81          | ~ (v1_relat_1 @ X12))),
% 15.59/15.81      inference('cnf', [status(esa)], [d18_relat_1])).
% 15.59/15.81  thf('86', plain,
% 15.59/15.81      (![X0 : $i, X1 : $i]:
% 15.59/15.81         ((zip_tseitin_0 @ sk_B_1 @ X1)
% 15.59/15.81          | ~ (v1_relat_1 @ sk_D)
% 15.59/15.81          | (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 15.59/15.81      inference('sup-', [status(thm)], ['84', '85'])).
% 15.59/15.81  thf('87', plain, ((v1_relat_1 @ sk_D)),
% 15.59/15.81      inference('sup-', [status(thm)], ['36', '37'])).
% 15.59/15.81  thf('88', plain,
% 15.59/15.81      (![X0 : $i, X1 : $i]:
% 15.59/15.81         ((zip_tseitin_0 @ sk_B_1 @ X1)
% 15.59/15.81          | (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 15.59/15.81      inference('demod', [status(thm)], ['86', '87'])).
% 15.59/15.81  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 15.59/15.81  thf('89', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 15.59/15.81      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.59/15.81  thf(d10_xboole_0, axiom,
% 15.59/15.81    (![A:$i,B:$i]:
% 15.59/15.81     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 15.59/15.81  thf('90', plain,
% 15.59/15.81      (![X4 : $i, X6 : $i]:
% 15.59/15.81         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 15.59/15.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.59/15.81  thf('91', plain,
% 15.59/15.81      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 15.59/15.81      inference('sup-', [status(thm)], ['89', '90'])).
% 15.59/15.81  thf('92', plain,
% 15.59/15.81      (![X0 : $i]:
% 15.59/15.81         ((zip_tseitin_0 @ sk_B_1 @ X0) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 15.59/15.81      inference('sup-', [status(thm)], ['88', '91'])).
% 15.59/15.81  thf('93', plain,
% 15.59/15.81      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 15.59/15.81        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 15.59/15.81      inference('sup-', [status(thm)], ['16', '17'])).
% 15.59/15.81  thf('94', plain,
% 15.59/15.81      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 15.59/15.81        | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 15.59/15.81      inference('sup-', [status(thm)], ['92', '93'])).
% 15.59/15.81  thf('95', plain,
% 15.59/15.81      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 15.59/15.81        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 15.59/15.81      inference('demod', [status(thm)], ['22', '25'])).
% 15.59/15.81  thf('96', plain,
% 15.59/15.81      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 15.59/15.81        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 15.59/15.81      inference('sup-', [status(thm)], ['94', '95'])).
% 15.59/15.81  thf('97', plain,
% 15.59/15.81      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('98', plain, (((sk_B_1) = (k1_xboole_0))),
% 15.59/15.81      inference('demod', [status(thm)], ['68', '72'])).
% 15.59/15.81  thf('99', plain,
% 15.59/15.81      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 15.59/15.81      inference('simplify', [status(thm)], ['76'])).
% 15.59/15.81  thf('100', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 15.59/15.81      inference('demod', [status(thm)], ['97', '98', '99'])).
% 15.59/15.81  thf('101', plain,
% 15.59/15.81      (![X0 : $i, X1 : $i]:
% 15.59/15.81         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 15.59/15.81          | (v4_relat_1 @ X1 @ X0))),
% 15.59/15.81      inference('sup-', [status(thm)], ['81', '82'])).
% 15.59/15.81  thf('102', plain, (![X0 : $i]: (v4_relat_1 @ sk_C_2 @ X0)),
% 15.59/15.81      inference('sup-', [status(thm)], ['100', '101'])).
% 15.59/15.81  thf('103', plain,
% 15.59/15.81      (![X12 : $i, X13 : $i]:
% 15.59/15.81         (~ (v4_relat_1 @ X12 @ X13)
% 15.59/15.81          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 15.59/15.81          | ~ (v1_relat_1 @ X12))),
% 15.59/15.81      inference('cnf', [status(esa)], [d18_relat_1])).
% 15.59/15.81  thf('104', plain,
% 15.59/15.81      (![X0 : $i]:
% 15.59/15.81         (~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k1_relat_1 @ sk_C_2) @ X0))),
% 15.59/15.81      inference('sup-', [status(thm)], ['102', '103'])).
% 15.59/15.81  thf('105', plain, ((v1_relat_1 @ sk_C_2)),
% 15.59/15.81      inference('sup-', [status(thm)], ['30', '31'])).
% 15.59/15.81  thf('106', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ sk_C_2) @ X0)),
% 15.59/15.81      inference('demod', [status(thm)], ['104', '105'])).
% 15.59/15.81  thf('107', plain,
% 15.59/15.81      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 15.59/15.81      inference('sup-', [status(thm)], ['89', '90'])).
% 15.59/15.81  thf('108', plain, (((k1_relat_1 @ sk_C_2) = (k1_xboole_0))),
% 15.59/15.81      inference('sup-', [status(thm)], ['106', '107'])).
% 15.59/15.81  thf('109', plain,
% 15.59/15.81      ((((k1_relat_1 @ sk_D) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 15.59/15.81      inference('demod', [status(thm)], ['96', '108'])).
% 15.59/15.81  thf('110', plain,
% 15.59/15.81      (![X0 : $i]:
% 15.59/15.81         ((zip_tseitin_0 @ sk_B_1 @ X0) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 15.59/15.81      inference('sup-', [status(thm)], ['88', '91'])).
% 15.59/15.81  thf('111', plain,
% 15.59/15.81      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 15.59/15.81        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 15.59/15.81      inference('sup-', [status(thm)], ['2', '3'])).
% 15.59/15.81  thf('112', plain,
% 15.59/15.81      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 15.59/15.81        | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 15.59/15.81      inference('sup-', [status(thm)], ['110', '111'])).
% 15.59/15.81  thf('113', plain,
% 15.59/15.81      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 15.59/15.81        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.59/15.81      inference('demod', [status(thm)], ['8', '11'])).
% 15.59/15.81  thf('114', plain,
% 15.59/15.81      ((((k1_relat_1 @ sk_D) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 15.59/15.81      inference('sup-', [status(thm)], ['112', '113'])).
% 15.59/15.81  thf('115', plain,
% 15.59/15.81      ((((sk_A) != (k1_xboole_0)) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 15.59/15.81      inference('eq_fact', [status(thm)], ['114'])).
% 15.59/15.81  thf('116', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 15.59/15.81      inference('clc', [status(thm)], ['109', '115'])).
% 15.59/15.81  thf('117', plain, (((k1_relat_1 @ sk_C_2) = (k1_xboole_0))),
% 15.59/15.81      inference('sup-', [status(thm)], ['106', '107'])).
% 15.59/15.81  thf('118', plain,
% 15.59/15.81      (![X14 : $i, X15 : $i]:
% 15.59/15.81         (~ (v1_relat_1 @ X14)
% 15.59/15.81          | ~ (v1_funct_1 @ X14)
% 15.59/15.81          | ((X15) = (X14))
% 15.59/15.81          | (r2_hidden @ (sk_C_1 @ X14 @ X15) @ (k1_relat_1 @ X15))
% 15.59/15.81          | ((k1_relat_1 @ X15) != (k1_relat_1 @ X14))
% 15.59/15.81          | ~ (v1_funct_1 @ X15)
% 15.59/15.81          | ~ (v1_relat_1 @ X15))),
% 15.59/15.81      inference('cnf', [status(esa)], [t9_funct_1])).
% 15.59/15.81  thf('119', plain,
% 15.59/15.81      (![X0 : $i]:
% 15.59/15.81         (((k1_xboole_0) != (k1_relat_1 @ X0))
% 15.59/15.81          | ~ (v1_relat_1 @ sk_C_2)
% 15.59/15.81          | ~ (v1_funct_1 @ sk_C_2)
% 15.59/15.81          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 15.59/15.81          | ((sk_C_2) = (X0))
% 15.59/15.81          | ~ (v1_funct_1 @ X0)
% 15.59/15.81          | ~ (v1_relat_1 @ X0))),
% 15.59/15.81      inference('sup-', [status(thm)], ['117', '118'])).
% 15.59/15.81  thf('120', plain, ((v1_relat_1 @ sk_C_2)),
% 15.59/15.81      inference('sup-', [status(thm)], ['30', '31'])).
% 15.59/15.81  thf('121', plain, ((v1_funct_1 @ sk_C_2)),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('122', plain, (((k1_relat_1 @ sk_C_2) = (k1_xboole_0))),
% 15.59/15.81      inference('sup-', [status(thm)], ['106', '107'])).
% 15.59/15.81  thf('123', plain,
% 15.59/15.81      (![X0 : $i]:
% 15.59/15.81         (((k1_xboole_0) != (k1_relat_1 @ X0))
% 15.59/15.81          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ k1_xboole_0)
% 15.59/15.81          | ((sk_C_2) = (X0))
% 15.59/15.81          | ~ (v1_funct_1 @ X0)
% 15.59/15.81          | ~ (v1_relat_1 @ X0))),
% 15.59/15.81      inference('demod', [status(thm)], ['119', '120', '121', '122'])).
% 15.59/15.81  thf('124', plain,
% 15.59/15.81      ((((k1_xboole_0) != (k1_xboole_0))
% 15.59/15.81        | ~ (v1_relat_1 @ sk_D)
% 15.59/15.81        | ~ (v1_funct_1 @ sk_D)
% 15.59/15.81        | ((sk_C_2) = (sk_D))
% 15.59/15.81        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ k1_xboole_0))),
% 15.59/15.81      inference('sup-', [status(thm)], ['116', '123'])).
% 15.59/15.81  thf('125', plain, ((v1_relat_1 @ sk_D)),
% 15.59/15.81      inference('sup-', [status(thm)], ['36', '37'])).
% 15.59/15.81  thf('126', plain, ((v1_funct_1 @ sk_D)),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('127', plain,
% 15.59/15.81      ((((k1_xboole_0) != (k1_xboole_0))
% 15.59/15.81        | ((sk_C_2) = (sk_D))
% 15.59/15.81        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ k1_xboole_0))),
% 15.59/15.81      inference('demod', [status(thm)], ['124', '125', '126'])).
% 15.59/15.81  thf('128', plain,
% 15.59/15.81      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ k1_xboole_0)
% 15.59/15.81        | ((sk_C_2) = (sk_D)))),
% 15.59/15.81      inference('simplify', [status(thm)], ['127'])).
% 15.59/15.81  thf('129', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 15.59/15.81      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.59/15.81  thf('130', plain,
% 15.59/15.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.59/15.81         (~ (r2_hidden @ X0 @ X1)
% 15.59/15.81          | (r2_hidden @ X0 @ X2)
% 15.59/15.81          | ~ (r1_tarski @ X1 @ X2))),
% 15.59/15.81      inference('cnf', [status(esa)], [d3_tarski])).
% 15.59/15.81  thf('131', plain,
% 15.59/15.81      (![X0 : $i, X1 : $i]:
% 15.59/15.81         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 15.59/15.81      inference('sup-', [status(thm)], ['129', '130'])).
% 15.59/15.81  thf('132', plain,
% 15.59/15.81      (![X0 : $i]:
% 15.59/15.81         (((sk_C_2) = (sk_D)) | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ X0))),
% 15.59/15.81      inference('sup-', [status(thm)], ['128', '131'])).
% 15.59/15.81  thf('133', plain, (((k1_relat_1 @ sk_C_2) = (k1_xboole_0))),
% 15.59/15.81      inference('sup-', [status(thm)], ['106', '107'])).
% 15.59/15.81  thf('134', plain,
% 15.59/15.81      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 15.59/15.81        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 15.59/15.81      inference('sup-', [status(thm)], ['94', '95'])).
% 15.59/15.81  thf('135', plain,
% 15.59/15.81      (![X14 : $i, X15 : $i]:
% 15.59/15.81         (~ (v1_relat_1 @ X14)
% 15.59/15.81          | ~ (v1_funct_1 @ X14)
% 15.59/15.81          | ((X15) = (X14))
% 15.59/15.81          | (r2_hidden @ (sk_C_1 @ X14 @ X15) @ (k1_relat_1 @ X15))
% 15.59/15.81          | ((k1_relat_1 @ X15) != (k1_relat_1 @ X14))
% 15.59/15.81          | ~ (v1_funct_1 @ X15)
% 15.59/15.81          | ~ (v1_relat_1 @ X15))),
% 15.59/15.81      inference('cnf', [status(esa)], [t9_funct_1])).
% 15.59/15.81  thf('136', plain,
% 15.59/15.81      (![X0 : $i]:
% 15.59/15.81         (((k1_xboole_0) != (k1_relat_1 @ X0))
% 15.59/15.81          | ((sk_A) = (k1_relat_1 @ sk_C_2))
% 15.59/15.81          | ~ (v1_relat_1 @ sk_D)
% 15.59/15.81          | ~ (v1_funct_1 @ sk_D)
% 15.59/15.81          | (r2_hidden @ (sk_C_1 @ X0 @ sk_D) @ (k1_relat_1 @ sk_D))
% 15.59/15.81          | ((sk_D) = (X0))
% 15.59/15.81          | ~ (v1_funct_1 @ X0)
% 15.59/15.81          | ~ (v1_relat_1 @ X0))),
% 15.59/15.81      inference('sup-', [status(thm)], ['134', '135'])).
% 15.59/15.81  thf('137', plain, ((v1_relat_1 @ sk_D)),
% 15.59/15.81      inference('sup-', [status(thm)], ['36', '37'])).
% 15.59/15.81  thf('138', plain, ((v1_funct_1 @ sk_D)),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('139', plain,
% 15.59/15.81      (![X0 : $i]:
% 15.59/15.81         (((k1_xboole_0) != (k1_relat_1 @ X0))
% 15.59/15.81          | ((sk_A) = (k1_relat_1 @ sk_C_2))
% 15.59/15.81          | (r2_hidden @ (sk_C_1 @ X0 @ sk_D) @ (k1_relat_1 @ sk_D))
% 15.59/15.81          | ((sk_D) = (X0))
% 15.59/15.81          | ~ (v1_funct_1 @ X0)
% 15.59/15.81          | ~ (v1_relat_1 @ X0))),
% 15.59/15.81      inference('demod', [status(thm)], ['136', '137', '138'])).
% 15.59/15.81  thf('140', plain, (((k1_relat_1 @ sk_C_2) = (k1_xboole_0))),
% 15.59/15.81      inference('sup-', [status(thm)], ['106', '107'])).
% 15.59/15.81  thf('141', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 15.59/15.81      inference('clc', [status(thm)], ['109', '115'])).
% 15.59/15.81  thf('142', plain,
% 15.59/15.81      (![X0 : $i]:
% 15.59/15.81         (((k1_xboole_0) != (k1_relat_1 @ X0))
% 15.59/15.81          | ((sk_A) = (k1_xboole_0))
% 15.59/15.81          | (r2_hidden @ (sk_C_1 @ X0 @ sk_D) @ k1_xboole_0)
% 15.59/15.81          | ((sk_D) = (X0))
% 15.59/15.81          | ~ (v1_funct_1 @ X0)
% 15.59/15.81          | ~ (v1_relat_1 @ X0))),
% 15.59/15.81      inference('demod', [status(thm)], ['139', '140', '141'])).
% 15.59/15.81  thf('143', plain,
% 15.59/15.81      ((((k1_xboole_0) != (k1_xboole_0))
% 15.59/15.81        | ~ (v1_relat_1 @ sk_C_2)
% 15.59/15.81        | ~ (v1_funct_1 @ sk_C_2)
% 15.59/15.81        | ((sk_D) = (sk_C_2))
% 15.59/15.81        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_D) @ k1_xboole_0)
% 15.59/15.81        | ((sk_A) = (k1_xboole_0)))),
% 15.59/15.81      inference('sup-', [status(thm)], ['133', '142'])).
% 15.59/15.81  thf('144', plain, ((v1_relat_1 @ sk_C_2)),
% 15.59/15.81      inference('sup-', [status(thm)], ['30', '31'])).
% 15.59/15.81  thf('145', plain, ((v1_funct_1 @ sk_C_2)),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('146', plain,
% 15.59/15.81      ((((k1_xboole_0) != (k1_xboole_0))
% 15.59/15.81        | ((sk_D) = (sk_C_2))
% 15.59/15.81        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_D) @ k1_xboole_0)
% 15.59/15.81        | ((sk_A) = (k1_xboole_0)))),
% 15.59/15.81      inference('demod', [status(thm)], ['143', '144', '145'])).
% 15.59/15.81  thf('147', plain,
% 15.59/15.81      ((((sk_A) = (k1_xboole_0))
% 15.59/15.81        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_D) @ k1_xboole_0)
% 15.59/15.81        | ((sk_D) = (sk_C_2)))),
% 15.59/15.81      inference('simplify', [status(thm)], ['146'])).
% 15.59/15.81  thf('148', plain,
% 15.59/15.81      (![X0 : $i, X1 : $i]:
% 15.59/15.81         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 15.59/15.81      inference('sup-', [status(thm)], ['129', '130'])).
% 15.59/15.81  thf('149', plain,
% 15.59/15.81      (![X0 : $i]:
% 15.59/15.81         (((sk_D) = (sk_C_2))
% 15.59/15.81          | ((sk_A) = (k1_xboole_0))
% 15.59/15.81          | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_D) @ X0))),
% 15.59/15.81      inference('sup-', [status(thm)], ['147', '148'])).
% 15.59/15.81  thf('150', plain,
% 15.59/15.81      (![X37 : $i]:
% 15.59/15.81         (((k1_funct_1 @ sk_C_2 @ X37) = (k1_funct_1 @ sk_D @ X37))
% 15.59/15.81          | ~ (r2_hidden @ X37 @ sk_A))),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('151', plain,
% 15.59/15.81      ((((sk_A) = (k1_xboole_0))
% 15.59/15.81        | ((sk_D) = (sk_C_2))
% 15.59/15.81        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_D))
% 15.59/15.81            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_C_2 @ sk_D))))),
% 15.59/15.81      inference('sup-', [status(thm)], ['149', '150'])).
% 15.59/15.81  thf('152', plain,
% 15.59/15.81      ((((sk_A) = (k1_xboole_0))
% 15.59/15.81        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_D))
% 15.59/15.81            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_C_2 @ sk_D))))),
% 15.59/15.81      inference('condensation', [status(thm)], ['151'])).
% 15.59/15.81  thf('153', plain,
% 15.59/15.81      (![X14 : $i, X15 : $i]:
% 15.59/15.81         (~ (v1_relat_1 @ X14)
% 15.59/15.81          | ~ (v1_funct_1 @ X14)
% 15.59/15.81          | ((X15) = (X14))
% 15.59/15.81          | ((k1_funct_1 @ X15 @ (sk_C_1 @ X14 @ X15))
% 15.59/15.81              != (k1_funct_1 @ X14 @ (sk_C_1 @ X14 @ X15)))
% 15.59/15.81          | ((k1_relat_1 @ X15) != (k1_relat_1 @ X14))
% 15.59/15.81          | ~ (v1_funct_1 @ X15)
% 15.59/15.81          | ~ (v1_relat_1 @ X15))),
% 15.59/15.81      inference('cnf', [status(esa)], [t9_funct_1])).
% 15.59/15.81  thf('154', plain,
% 15.59/15.81      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_D))
% 15.59/15.81          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_D)))
% 15.59/15.81        | ((sk_A) = (k1_xboole_0))
% 15.59/15.81        | ~ (v1_relat_1 @ sk_D)
% 15.59/15.81        | ~ (v1_funct_1 @ sk_D)
% 15.59/15.81        | ((k1_relat_1 @ sk_D) != (k1_relat_1 @ sk_C_2))
% 15.59/15.81        | ((sk_D) = (sk_C_2))
% 15.59/15.81        | ~ (v1_funct_1 @ sk_C_2)
% 15.59/15.81        | ~ (v1_relat_1 @ sk_C_2))),
% 15.59/15.81      inference('sup-', [status(thm)], ['152', '153'])).
% 15.59/15.81  thf('155', plain, ((v1_relat_1 @ sk_D)),
% 15.59/15.81      inference('sup-', [status(thm)], ['36', '37'])).
% 15.59/15.81  thf('156', plain, ((v1_funct_1 @ sk_D)),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('157', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 15.59/15.81      inference('clc', [status(thm)], ['109', '115'])).
% 15.59/15.81  thf('158', plain, (((k1_relat_1 @ sk_C_2) = (k1_xboole_0))),
% 15.59/15.81      inference('sup-', [status(thm)], ['106', '107'])).
% 15.59/15.81  thf('159', plain, ((v1_funct_1 @ sk_C_2)),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('160', plain, ((v1_relat_1 @ sk_C_2)),
% 15.59/15.81      inference('sup-', [status(thm)], ['30', '31'])).
% 15.59/15.81  thf('161', plain,
% 15.59/15.81      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_D))
% 15.59/15.81          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_D)))
% 15.59/15.81        | ((sk_A) = (k1_xboole_0))
% 15.59/15.81        | ((k1_xboole_0) != (k1_xboole_0))
% 15.59/15.81        | ((sk_D) = (sk_C_2)))),
% 15.59/15.81      inference('demod', [status(thm)],
% 15.59/15.81                ['154', '155', '156', '157', '158', '159', '160'])).
% 15.59/15.81  thf('162', plain, ((((sk_D) = (sk_C_2)) | ((sk_A) = (k1_xboole_0)))),
% 15.59/15.81      inference('simplify', [status(thm)], ['161'])).
% 15.59/15.81  thf('163', plain,
% 15.59/15.81      (![X37 : $i]:
% 15.59/15.81         (((k1_funct_1 @ sk_C_2 @ X37) = (k1_funct_1 @ sk_D @ X37))
% 15.59/15.81          | ~ (r2_hidden @ X37 @ sk_A))),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('164', plain,
% 15.59/15.81      (![X0 : $i]:
% 15.59/15.81         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 15.59/15.81          | ((sk_D) = (sk_C_2))
% 15.59/15.81          | ((k1_funct_1 @ sk_C_2 @ X0) = (k1_funct_1 @ sk_D @ X0)))),
% 15.59/15.81      inference('sup-', [status(thm)], ['162', '163'])).
% 15.59/15.81  thf('165', plain,
% 15.59/15.81      (![X0 : $i]:
% 15.59/15.81         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 15.59/15.81          | ((k1_funct_1 @ sk_C_2 @ X0) = (k1_funct_1 @ sk_D @ X0)))),
% 15.59/15.81      inference('condensation', [status(thm)], ['164'])).
% 15.59/15.81  thf('166', plain,
% 15.59/15.81      ((((sk_C_2) = (sk_D))
% 15.59/15.81        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 15.59/15.81            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 15.59/15.81      inference('sup-', [status(thm)], ['132', '165'])).
% 15.59/15.81  thf('167', plain,
% 15.59/15.81      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 15.59/15.81         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 15.59/15.81      inference('condensation', [status(thm)], ['166'])).
% 15.59/15.81  thf('168', plain,
% 15.59/15.81      (![X14 : $i, X15 : $i]:
% 15.59/15.81         (~ (v1_relat_1 @ X14)
% 15.59/15.81          | ~ (v1_funct_1 @ X14)
% 15.59/15.81          | ((X15) = (X14))
% 15.59/15.81          | ((k1_funct_1 @ X15 @ (sk_C_1 @ X14 @ X15))
% 15.59/15.81              != (k1_funct_1 @ X14 @ (sk_C_1 @ X14 @ X15)))
% 15.59/15.81          | ((k1_relat_1 @ X15) != (k1_relat_1 @ X14))
% 15.59/15.81          | ~ (v1_funct_1 @ X15)
% 15.59/15.81          | ~ (v1_relat_1 @ X15))),
% 15.59/15.81      inference('cnf', [status(esa)], [t9_funct_1])).
% 15.59/15.81  thf('169', plain,
% 15.59/15.81      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 15.59/15.81          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 15.59/15.81        | ~ (v1_relat_1 @ sk_C_2)
% 15.59/15.81        | ~ (v1_funct_1 @ sk_C_2)
% 15.59/15.81        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 15.59/15.81        | ((sk_C_2) = (sk_D))
% 15.59/15.81        | ~ (v1_funct_1 @ sk_D)
% 15.59/15.81        | ~ (v1_relat_1 @ sk_D))),
% 15.59/15.81      inference('sup-', [status(thm)], ['167', '168'])).
% 15.59/15.81  thf('170', plain, ((v1_relat_1 @ sk_C_2)),
% 15.59/15.81      inference('sup-', [status(thm)], ['30', '31'])).
% 15.59/15.81  thf('171', plain, ((v1_funct_1 @ sk_C_2)),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('172', plain, (((k1_relat_1 @ sk_C_2) = (k1_xboole_0))),
% 15.59/15.81      inference('sup-', [status(thm)], ['106', '107'])).
% 15.59/15.81  thf('173', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 15.59/15.81      inference('clc', [status(thm)], ['109', '115'])).
% 15.59/15.81  thf('174', plain, ((v1_funct_1 @ sk_D)),
% 15.59/15.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.59/15.81  thf('175', plain, ((v1_relat_1 @ sk_D)),
% 15.59/15.81      inference('sup-', [status(thm)], ['36', '37'])).
% 15.59/15.81  thf('176', plain,
% 15.59/15.81      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 15.59/15.81          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 15.59/15.81        | ((k1_xboole_0) != (k1_xboole_0))
% 15.59/15.81        | ((sk_C_2) = (sk_D)))),
% 15.59/15.81      inference('demod', [status(thm)],
% 15.59/15.81                ['169', '170', '171', '172', '173', '174', '175'])).
% 15.59/15.81  thf('177', plain, (((sk_C_2) = (sk_D))),
% 15.59/15.81      inference('simplify', [status(thm)], ['176'])).
% 15.59/15.81  thf('178', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 15.59/15.81      inference('demod', [status(thm)], ['97', '98', '99'])).
% 15.59/15.81  thf('179', plain,
% 15.59/15.81      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 15.59/15.81      inference('simplify', [status(thm)], ['76'])).
% 15.59/15.81  thf('180', plain,
% 15.59/15.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.59/15.81         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 15.59/15.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 15.59/15.81      inference('condensation', [status(thm)], ['70'])).
% 15.59/15.81  thf('181', plain,
% 15.59/15.81      (![X0 : $i, X1 : $i]:
% 15.59/15.81         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 15.59/15.81          | (r2_relset_1 @ X0 @ k1_xboole_0 @ X1 @ X1))),
% 15.59/15.81      inference('sup-', [status(thm)], ['179', '180'])).
% 15.59/15.81  thf('182', plain,
% 15.59/15.81      (![X0 : $i]: (r2_relset_1 @ X0 @ k1_xboole_0 @ sk_C_2 @ sk_C_2)),
% 15.59/15.81      inference('sup-', [status(thm)], ['178', '181'])).
% 15.59/15.81  thf('183', plain, ($false),
% 15.59/15.81      inference('demod', [status(thm)], ['74', '177', '182'])).
% 15.59/15.81  
% 15.59/15.81  % SZS output end Refutation
% 15.59/15.81  
% 15.59/15.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

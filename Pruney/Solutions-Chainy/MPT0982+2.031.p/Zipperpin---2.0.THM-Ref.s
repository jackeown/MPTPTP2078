%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mTiKjxaph4

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:59 EST 2020

% Result     : Theorem 28.26s
% Output     : Refutation 28.26s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 390 expanded)
%              Number of leaves         :   42 ( 130 expanded)
%              Depth                    :   20
%              Number of atoms          : 1594 (7613 expanded)
%              Number of equality atoms :   64 ( 380 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(t28_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                = C )
              & ( v2_funct_1 @ E ) )
           => ( ( C = k1_xboole_0 )
              | ( ( k2_relset_1 @ A @ B @ D )
                = B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ B @ C )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                  = C )
                & ( v2_funct_1 @ E ) )
             => ( ( C = k1_xboole_0 )
                | ( ( k2_relset_1 @ A @ B @ D )
                  = B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['4','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('15',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('23',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('28',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 )
        = ( k5_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['25','34'])).

thf(t51_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
                = ( k2_relat_1 @ A ) )
              & ( v2_funct_1 @ A ) )
           => ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ X10 ) @ ( k2_relat_1 @ X9 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) )
       != ( k2_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t51_funct_1])).

thf('37',plain,
    ( ( sk_C
     != ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ( r1_tarski @ ( k1_relat_1 @ sk_E ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('42',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('46',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('47',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('48',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('49',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('50',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('51',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('56',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('57',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['47','54','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('61',plain,
    ( ( sk_C
     != ( k2_relat_1 @ sk_E ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['37','42','43','44','58','59','60'])).

thf('62',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['25','34'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['63'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('65',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X40 ) @ X41 )
      | ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X40 ) @ X41 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('68',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 )
        = ( k5_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('75',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X1 @ X0 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X1 @ X0 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( m1_subset_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['72','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('87',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C )
    | ( ( k2_relat_1 @ sk_E )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['62','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('98',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('100',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['40','41'])).

thf('102',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['25','34'])).

thf('104',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['40','41'])).

thf('106',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('108',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['95','102','103','104','105','106','107'])).

thf('109',plain,
    ( ( sk_C != sk_C )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['61','108'])).

thf('110',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['12','110'])).

thf('112',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('115',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['112','115'])).

thf('117',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['111','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mTiKjxaph4
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:09:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 28.26/28.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 28.26/28.43  % Solved by: fo/fo7.sh
% 28.26/28.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 28.26/28.43  % done 6007 iterations in 27.973s
% 28.26/28.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 28.26/28.43  % SZS output start Refutation
% 28.26/28.43  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 28.26/28.43  thf(sk_A_type, type, sk_A: $i).
% 28.26/28.43  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 28.26/28.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 28.26/28.43  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 28.26/28.43  thf(sk_E_type, type, sk_E: $i).
% 28.26/28.43  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 28.26/28.43  thf(sk_B_type, type, sk_B: $i).
% 28.26/28.43  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 28.26/28.43  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 28.26/28.43  thf(sk_C_type, type, sk_C: $i).
% 28.26/28.43  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 28.26/28.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 28.26/28.43  thf(sk_D_type, type, sk_D: $i).
% 28.26/28.43  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 28.26/28.43  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 28.26/28.43  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 28.26/28.43  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 28.26/28.43  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 28.26/28.43  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 28.26/28.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 28.26/28.43  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 28.26/28.43  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 28.26/28.43  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 28.26/28.43  thf(t28_funct_2, conjecture,
% 28.26/28.43    (![A:$i,B:$i,C:$i,D:$i]:
% 28.26/28.43     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 28.26/28.43         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 28.26/28.43       ( ![E:$i]:
% 28.26/28.43         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 28.26/28.43             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 28.26/28.43           ( ( ( ( k2_relset_1 @
% 28.26/28.43                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 28.26/28.43                 ( C ) ) & 
% 28.26/28.43               ( v2_funct_1 @ E ) ) =>
% 28.26/28.43             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 28.26/28.43               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 28.26/28.43  thf(zf_stmt_0, negated_conjecture,
% 28.26/28.43    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 28.26/28.43        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 28.26/28.43            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 28.26/28.43          ( ![E:$i]:
% 28.26/28.43            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 28.26/28.43                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 28.26/28.43              ( ( ( ( k2_relset_1 @
% 28.26/28.43                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 28.26/28.43                    ( C ) ) & 
% 28.26/28.43                  ( v2_funct_1 @ E ) ) =>
% 28.26/28.43                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 28.26/28.43                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 28.26/28.43    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 28.26/28.43  thf('0', plain,
% 28.26/28.43      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.43  thf(cc2_relset_1, axiom,
% 28.26/28.43    (![A:$i,B:$i,C:$i]:
% 28.26/28.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 28.26/28.43       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 28.26/28.43  thf('1', plain,
% 28.26/28.43      (![X11 : $i, X12 : $i, X13 : $i]:
% 28.26/28.43         ((v5_relat_1 @ X11 @ X13)
% 28.26/28.43          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 28.26/28.43      inference('cnf', [status(esa)], [cc2_relset_1])).
% 28.26/28.43  thf('2', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 28.26/28.43      inference('sup-', [status(thm)], ['0', '1'])).
% 28.26/28.43  thf(d19_relat_1, axiom,
% 28.26/28.43    (![A:$i,B:$i]:
% 28.26/28.43     ( ( v1_relat_1 @ B ) =>
% 28.26/28.43       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 28.26/28.43  thf('3', plain,
% 28.26/28.43      (![X5 : $i, X6 : $i]:
% 28.26/28.43         (~ (v5_relat_1 @ X5 @ X6)
% 28.26/28.43          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 28.26/28.43          | ~ (v1_relat_1 @ X5))),
% 28.26/28.43      inference('cnf', [status(esa)], [d19_relat_1])).
% 28.26/28.43  thf('4', plain,
% 28.26/28.43      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 28.26/28.43      inference('sup-', [status(thm)], ['2', '3'])).
% 28.26/28.43  thf('5', plain,
% 28.26/28.43      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.43  thf(cc2_relat_1, axiom,
% 28.26/28.43    (![A:$i]:
% 28.26/28.43     ( ( v1_relat_1 @ A ) =>
% 28.26/28.43       ( ![B:$i]:
% 28.26/28.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 28.26/28.43  thf('6', plain,
% 28.26/28.43      (![X3 : $i, X4 : $i]:
% 28.26/28.43         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 28.26/28.43          | (v1_relat_1 @ X3)
% 28.26/28.43          | ~ (v1_relat_1 @ X4))),
% 28.26/28.43      inference('cnf', [status(esa)], [cc2_relat_1])).
% 28.26/28.43  thf('7', plain,
% 28.26/28.43      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 28.26/28.43      inference('sup-', [status(thm)], ['5', '6'])).
% 28.26/28.43  thf(fc6_relat_1, axiom,
% 28.26/28.43    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 28.26/28.43  thf('8', plain,
% 28.26/28.43      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 28.26/28.43      inference('cnf', [status(esa)], [fc6_relat_1])).
% 28.26/28.43  thf('9', plain, ((v1_relat_1 @ sk_D)),
% 28.26/28.43      inference('demod', [status(thm)], ['7', '8'])).
% 28.26/28.43  thf('10', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 28.26/28.43      inference('demod', [status(thm)], ['4', '9'])).
% 28.26/28.43  thf(d10_xboole_0, axiom,
% 28.26/28.43    (![A:$i,B:$i]:
% 28.26/28.43     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 28.26/28.43  thf('11', plain,
% 28.26/28.43      (![X0 : $i, X2 : $i]:
% 28.26/28.43         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 28.26/28.43      inference('cnf', [status(esa)], [d10_xboole_0])).
% 28.26/28.43  thf('12', plain,
% 28.26/28.43      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))
% 28.26/28.43        | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 28.26/28.43      inference('sup-', [status(thm)], ['10', '11'])).
% 28.26/28.43  thf('13', plain,
% 28.26/28.43      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.43  thf('14', plain,
% 28.26/28.43      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.43  thf(dt_k1_partfun1, axiom,
% 28.26/28.43    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 28.26/28.43     ( ( ( v1_funct_1 @ E ) & 
% 28.26/28.43         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 28.26/28.43         ( v1_funct_1 @ F ) & 
% 28.26/28.43         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 28.26/28.43       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 28.26/28.43         ( m1_subset_1 @
% 28.26/28.43           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 28.26/28.43           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 28.26/28.43  thf('15', plain,
% 28.26/28.43      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 28.26/28.43         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 28.26/28.43          | ~ (v1_funct_1 @ X28)
% 28.26/28.43          | ~ (v1_funct_1 @ X31)
% 28.26/28.43          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 28.26/28.43          | (m1_subset_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31) @ 
% 28.26/28.43             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X33))))),
% 28.26/28.43      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 28.26/28.43  thf('16', plain,
% 28.26/28.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.26/28.43         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 28.26/28.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 28.26/28.43          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 28.26/28.43          | ~ (v1_funct_1 @ X1)
% 28.26/28.43          | ~ (v1_funct_1 @ sk_D))),
% 28.26/28.43      inference('sup-', [status(thm)], ['14', '15'])).
% 28.26/28.43  thf('17', plain, ((v1_funct_1 @ sk_D)),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.43  thf('18', plain,
% 28.26/28.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.26/28.43         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 28.26/28.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 28.26/28.43          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 28.26/28.43          | ~ (v1_funct_1 @ X1))),
% 28.26/28.43      inference('demod', [status(thm)], ['16', '17'])).
% 28.26/28.43  thf('19', plain,
% 28.26/28.43      ((~ (v1_funct_1 @ sk_E)
% 28.26/28.43        | (m1_subset_1 @ 
% 28.26/28.43           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 28.26/28.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 28.26/28.43      inference('sup-', [status(thm)], ['13', '18'])).
% 28.26/28.43  thf('20', plain, ((v1_funct_1 @ sk_E)),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.43  thf('21', plain,
% 28.26/28.43      ((m1_subset_1 @ 
% 28.26/28.43        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 28.26/28.43        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 28.26/28.43      inference('demod', [status(thm)], ['19', '20'])).
% 28.26/28.43  thf(redefinition_k2_relset_1, axiom,
% 28.26/28.43    (![A:$i,B:$i,C:$i]:
% 28.26/28.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 28.26/28.43       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 28.26/28.43  thf('22', plain,
% 28.26/28.43      (![X17 : $i, X18 : $i, X19 : $i]:
% 28.26/28.43         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 28.26/28.43          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 28.26/28.43      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 28.26/28.43  thf('23', plain,
% 28.26/28.43      (((k2_relset_1 @ sk_A @ sk_C @ 
% 28.26/28.43         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))
% 28.26/28.43         = (k2_relat_1 @ 
% 28.26/28.43            (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 28.26/28.43      inference('sup-', [status(thm)], ['21', '22'])).
% 28.26/28.43  thf('24', plain,
% 28.26/28.43      (((k2_relset_1 @ sk_A @ sk_C @ 
% 28.26/28.43         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.43  thf('25', plain,
% 28.26/28.43      (((k2_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))
% 28.26/28.43         = (sk_C))),
% 28.26/28.43      inference('sup+', [status(thm)], ['23', '24'])).
% 28.26/28.43  thf('26', plain,
% 28.26/28.43      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.43  thf('27', plain,
% 28.26/28.43      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.43  thf(redefinition_k1_partfun1, axiom,
% 28.26/28.43    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 28.26/28.43     ( ( ( v1_funct_1 @ E ) & 
% 28.26/28.43         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 28.26/28.43         ( v1_funct_1 @ F ) & 
% 28.26/28.43         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 28.26/28.43       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 28.26/28.43  thf('28', plain,
% 28.26/28.43      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 28.26/28.43         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 28.26/28.43          | ~ (v1_funct_1 @ X34)
% 28.26/28.43          | ~ (v1_funct_1 @ X37)
% 28.26/28.43          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 28.26/28.43          | ((k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37)
% 28.26/28.43              = (k5_relat_1 @ X34 @ X37)))),
% 28.26/28.43      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 28.26/28.43  thf('29', plain,
% 28.26/28.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.26/28.43         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 28.26/28.43            = (k5_relat_1 @ sk_D @ X0))
% 28.26/28.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 28.26/28.43          | ~ (v1_funct_1 @ X0)
% 28.26/28.43          | ~ (v1_funct_1 @ sk_D))),
% 28.26/28.43      inference('sup-', [status(thm)], ['27', '28'])).
% 28.26/28.43  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.43  thf('31', plain,
% 28.26/28.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.26/28.43         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 28.26/28.43            = (k5_relat_1 @ sk_D @ X0))
% 28.26/28.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 28.26/28.43          | ~ (v1_funct_1 @ X0))),
% 28.26/28.43      inference('demod', [status(thm)], ['29', '30'])).
% 28.26/28.43  thf('32', plain,
% 28.26/28.43      ((~ (v1_funct_1 @ sk_E)
% 28.26/28.43        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 28.26/28.43            = (k5_relat_1 @ sk_D @ sk_E)))),
% 28.26/28.43      inference('sup-', [status(thm)], ['26', '31'])).
% 28.26/28.43  thf('33', plain, ((v1_funct_1 @ sk_E)),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.43  thf('34', plain,
% 28.26/28.43      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 28.26/28.43         = (k5_relat_1 @ sk_D @ sk_E))),
% 28.26/28.43      inference('demod', [status(thm)], ['32', '33'])).
% 28.26/28.43  thf('35', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 28.26/28.43      inference('demod', [status(thm)], ['25', '34'])).
% 28.26/28.43  thf(t51_funct_1, axiom,
% 28.26/28.43    (![A:$i]:
% 28.26/28.43     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 28.26/28.43       ( ![B:$i]:
% 28.26/28.43         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 28.26/28.43           ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) & 
% 28.26/28.43               ( v2_funct_1 @ A ) ) =>
% 28.26/28.43             ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 28.26/28.43  thf('36', plain,
% 28.26/28.43      (![X9 : $i, X10 : $i]:
% 28.26/28.43         (~ (v1_relat_1 @ X9)
% 28.26/28.43          | ~ (v1_funct_1 @ X9)
% 28.26/28.43          | (r1_tarski @ (k1_relat_1 @ X10) @ (k2_relat_1 @ X9))
% 28.26/28.43          | ((k2_relat_1 @ (k5_relat_1 @ X9 @ X10)) != (k2_relat_1 @ X10))
% 28.26/28.43          | ~ (v2_funct_1 @ X10)
% 28.26/28.43          | ~ (v1_funct_1 @ X10)
% 28.26/28.43          | ~ (v1_relat_1 @ X10))),
% 28.26/28.43      inference('cnf', [status(esa)], [t51_funct_1])).
% 28.26/28.43  thf('37', plain,
% 28.26/28.43      ((((sk_C) != (k2_relat_1 @ sk_E))
% 28.26/28.43        | ~ (v1_relat_1 @ sk_E)
% 28.26/28.43        | ~ (v1_funct_1 @ sk_E)
% 28.26/28.43        | ~ (v2_funct_1 @ sk_E)
% 28.26/28.43        | (r1_tarski @ (k1_relat_1 @ sk_E) @ (k2_relat_1 @ sk_D))
% 28.26/28.43        | ~ (v1_funct_1 @ sk_D)
% 28.26/28.43        | ~ (v1_relat_1 @ sk_D))),
% 28.26/28.43      inference('sup-', [status(thm)], ['35', '36'])).
% 28.26/28.43  thf('38', plain,
% 28.26/28.43      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.43  thf('39', plain,
% 28.26/28.43      (![X3 : $i, X4 : $i]:
% 28.26/28.43         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 28.26/28.43          | (v1_relat_1 @ X3)
% 28.26/28.43          | ~ (v1_relat_1 @ X4))),
% 28.26/28.43      inference('cnf', [status(esa)], [cc2_relat_1])).
% 28.26/28.43  thf('40', plain,
% 28.26/28.43      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_E))),
% 28.26/28.43      inference('sup-', [status(thm)], ['38', '39'])).
% 28.26/28.43  thf('41', plain,
% 28.26/28.43      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 28.26/28.43      inference('cnf', [status(esa)], [fc6_relat_1])).
% 28.26/28.43  thf('42', plain, ((v1_relat_1 @ sk_E)),
% 28.26/28.43      inference('demod', [status(thm)], ['40', '41'])).
% 28.26/28.43  thf('43', plain, ((v1_funct_1 @ sk_E)),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.43  thf('44', plain, ((v2_funct_1 @ sk_E)),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.43  thf('45', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.43  thf(d1_funct_2, axiom,
% 28.26/28.43    (![A:$i,B:$i,C:$i]:
% 28.26/28.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 28.26/28.43       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 28.26/28.43           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 28.26/28.43             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 28.26/28.43         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 28.26/28.43           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 28.26/28.43             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 28.26/28.43  thf(zf_stmt_1, axiom,
% 28.26/28.43    (![C:$i,B:$i,A:$i]:
% 28.26/28.43     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 28.26/28.43       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 28.26/28.43  thf('46', plain,
% 28.26/28.43      (![X22 : $i, X23 : $i, X24 : $i]:
% 28.26/28.43         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 28.26/28.43          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 28.26/28.43          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_1])).
% 28.26/28.43  thf('47', plain,
% 28.26/28.43      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 28.26/28.43        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 28.26/28.43      inference('sup-', [status(thm)], ['45', '46'])).
% 28.26/28.43  thf(zf_stmt_2, axiom,
% 28.26/28.43    (![B:$i,A:$i]:
% 28.26/28.43     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 28.26/28.43       ( zip_tseitin_0 @ B @ A ) ))).
% 28.26/28.43  thf('48', plain,
% 28.26/28.43      (![X20 : $i, X21 : $i]:
% 28.26/28.43         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_2])).
% 28.26/28.43  thf('49', plain,
% 28.26/28.43      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.43  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 28.26/28.43  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 28.26/28.43  thf(zf_stmt_5, axiom,
% 28.26/28.43    (![A:$i,B:$i,C:$i]:
% 28.26/28.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 28.26/28.43       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 28.26/28.43         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 28.26/28.43           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 28.26/28.43             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 28.26/28.43  thf('50', plain,
% 28.26/28.43      (![X25 : $i, X26 : $i, X27 : $i]:
% 28.26/28.43         (~ (zip_tseitin_0 @ X25 @ X26)
% 28.26/28.43          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 28.26/28.43          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_5])).
% 28.26/28.43  thf('51', plain,
% 28.26/28.43      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 28.26/28.43      inference('sup-', [status(thm)], ['49', '50'])).
% 28.26/28.43  thf('52', plain,
% 28.26/28.43      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 28.26/28.43      inference('sup-', [status(thm)], ['48', '51'])).
% 28.26/28.43  thf('53', plain, (((sk_C) != (k1_xboole_0))),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.43  thf('54', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 28.26/28.43      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 28.26/28.43  thf('55', plain,
% 28.26/28.43      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.43  thf(redefinition_k1_relset_1, axiom,
% 28.26/28.43    (![A:$i,B:$i,C:$i]:
% 28.26/28.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 28.26/28.43       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 28.26/28.43  thf('56', plain,
% 28.26/28.43      (![X14 : $i, X15 : $i, X16 : $i]:
% 28.26/28.43         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 28.26/28.43          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 28.26/28.43      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 28.26/28.43  thf('57', plain,
% 28.26/28.43      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 28.26/28.43      inference('sup-', [status(thm)], ['55', '56'])).
% 28.26/28.43  thf('58', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 28.26/28.43      inference('demod', [status(thm)], ['47', '54', '57'])).
% 28.26/28.43  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 28.26/28.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.43  thf('60', plain, ((v1_relat_1 @ sk_D)),
% 28.26/28.43      inference('demod', [status(thm)], ['7', '8'])).
% 28.26/28.43  thf('61', plain,
% 28.26/28.43      ((((sk_C) != (k2_relat_1 @ sk_E))
% 28.26/28.43        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D)))),
% 28.26/28.43      inference('demod', [status(thm)],
% 28.26/28.43                ['37', '42', '43', '44', '58', '59', '60'])).
% 28.26/28.43  thf('62', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 28.26/28.43      inference('demod', [status(thm)], ['25', '34'])).
% 28.26/28.43  thf('63', plain,
% 28.26/28.43      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 28.26/28.43      inference('cnf', [status(esa)], [d10_xboole_0])).
% 28.26/28.43  thf('64', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 28.26/28.43      inference('simplify', [status(thm)], ['63'])).
% 28.26/28.43  thf(t4_funct_2, axiom,
% 28.26/28.43    (![A:$i,B:$i]:
% 28.26/28.43     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 28.26/28.43       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 28.26/28.43         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 28.26/28.43           ( m1_subset_1 @
% 28.26/28.43             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 28.26/28.43  thf('65', plain,
% 28.26/28.43      (![X40 : $i, X41 : $i]:
% 28.26/28.43         (~ (r1_tarski @ (k2_relat_1 @ X40) @ X41)
% 28.26/28.43          | (m1_subset_1 @ X40 @ 
% 28.26/28.43             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X40) @ X41)))
% 28.26/28.43          | ~ (v1_funct_1 @ X40)
% 28.26/28.43          | ~ (v1_relat_1 @ X40))),
% 28.26/28.43      inference('cnf', [status(esa)], [t4_funct_2])).
% 28.26/28.43  thf('66', plain,
% 28.26/28.43      (![X0 : $i]:
% 28.26/28.43         (~ (v1_relat_1 @ X0)
% 28.26/28.43          | ~ (v1_funct_1 @ X0)
% 28.26/28.43          | (m1_subset_1 @ X0 @ 
% 28.26/28.43             (k1_zfmisc_1 @ 
% 28.26/28.43              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 28.26/28.43      inference('sup-', [status(thm)], ['64', '65'])).
% 28.26/28.43  thf('67', plain,
% 28.26/28.43      (![X0 : $i]:
% 28.26/28.43         (~ (v1_relat_1 @ X0)
% 28.26/28.43          | ~ (v1_funct_1 @ X0)
% 28.26/28.43          | (m1_subset_1 @ X0 @ 
% 28.26/28.43             (k1_zfmisc_1 @ 
% 28.26/28.43              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 28.26/28.43      inference('sup-', [status(thm)], ['64', '65'])).
% 28.26/28.43  thf('68', plain,
% 28.26/28.43      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 28.26/28.43         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 28.26/28.43          | ~ (v1_funct_1 @ X34)
% 28.26/28.43          | ~ (v1_funct_1 @ X37)
% 28.26/28.44          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 28.26/28.44          | ((k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37)
% 28.26/28.44              = (k5_relat_1 @ X34 @ X37)))),
% 28.26/28.44      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 28.26/28.44  thf('69', plain,
% 28.26/28.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 28.26/28.44         (~ (v1_funct_1 @ X0)
% 28.26/28.44          | ~ (v1_relat_1 @ X0)
% 28.26/28.44          | ((k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 28.26/28.44              X0 @ X1) = (k5_relat_1 @ X0 @ X1))
% 28.26/28.44          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 28.26/28.44          | ~ (v1_funct_1 @ X1)
% 28.26/28.44          | ~ (v1_funct_1 @ X0))),
% 28.26/28.44      inference('sup-', [status(thm)], ['67', '68'])).
% 28.26/28.44  thf('70', plain,
% 28.26/28.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 28.26/28.44         (~ (v1_funct_1 @ X1)
% 28.26/28.44          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 28.26/28.44          | ((k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 28.26/28.44              X0 @ X1) = (k5_relat_1 @ X0 @ X1))
% 28.26/28.44          | ~ (v1_relat_1 @ X0)
% 28.26/28.44          | ~ (v1_funct_1 @ X0))),
% 28.26/28.44      inference('simplify', [status(thm)], ['69'])).
% 28.26/28.44  thf('71', plain,
% 28.26/28.44      (![X0 : $i, X1 : $i]:
% 28.26/28.44         (~ (v1_funct_1 @ X0)
% 28.26/28.44          | ~ (v1_relat_1 @ X0)
% 28.26/28.44          | ~ (v1_funct_1 @ X1)
% 28.26/28.44          | ~ (v1_relat_1 @ X1)
% 28.26/28.44          | ((k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 28.26/28.44              (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0)
% 28.26/28.44              = (k5_relat_1 @ X1 @ X0))
% 28.26/28.44          | ~ (v1_funct_1 @ X0))),
% 28.26/28.44      inference('sup-', [status(thm)], ['66', '70'])).
% 28.26/28.44  thf('72', plain,
% 28.26/28.44      (![X0 : $i, X1 : $i]:
% 28.26/28.44         (((k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 28.26/28.44            (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0)
% 28.26/28.44            = (k5_relat_1 @ X1 @ X0))
% 28.26/28.44          | ~ (v1_relat_1 @ X1)
% 28.26/28.44          | ~ (v1_funct_1 @ X1)
% 28.26/28.44          | ~ (v1_relat_1 @ X0)
% 28.26/28.44          | ~ (v1_funct_1 @ X0))),
% 28.26/28.44      inference('simplify', [status(thm)], ['71'])).
% 28.26/28.44  thf('73', plain,
% 28.26/28.44      (![X0 : $i]:
% 28.26/28.44         (~ (v1_relat_1 @ X0)
% 28.26/28.44          | ~ (v1_funct_1 @ X0)
% 28.26/28.44          | (m1_subset_1 @ X0 @ 
% 28.26/28.44             (k1_zfmisc_1 @ 
% 28.26/28.44              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 28.26/28.44      inference('sup-', [status(thm)], ['64', '65'])).
% 28.26/28.44  thf('74', plain,
% 28.26/28.44      (![X0 : $i]:
% 28.26/28.44         (~ (v1_relat_1 @ X0)
% 28.26/28.44          | ~ (v1_funct_1 @ X0)
% 28.26/28.44          | (m1_subset_1 @ X0 @ 
% 28.26/28.44             (k1_zfmisc_1 @ 
% 28.26/28.44              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 28.26/28.44      inference('sup-', [status(thm)], ['64', '65'])).
% 28.26/28.44  thf('75', plain,
% 28.26/28.44      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 28.26/28.44         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 28.26/28.44          | ~ (v1_funct_1 @ X28)
% 28.26/28.44          | ~ (v1_funct_1 @ X31)
% 28.26/28.44          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 28.26/28.44          | (m1_subset_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31) @ 
% 28.26/28.44             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X33))))),
% 28.26/28.44      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 28.26/28.44  thf('76', plain,
% 28.26/28.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 28.26/28.44         (~ (v1_funct_1 @ X0)
% 28.26/28.44          | ~ (v1_relat_1 @ X0)
% 28.26/28.44          | (m1_subset_1 @ 
% 28.26/28.44             (k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X1 @ 
% 28.26/28.44              X0 @ X2) @ 
% 28.26/28.44             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 28.26/28.44          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 28.26/28.44          | ~ (v1_funct_1 @ X2)
% 28.26/28.44          | ~ (v1_funct_1 @ X0))),
% 28.26/28.44      inference('sup-', [status(thm)], ['74', '75'])).
% 28.26/28.44  thf('77', plain,
% 28.26/28.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 28.26/28.44         (~ (v1_funct_1 @ X2)
% 28.26/28.44          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 28.26/28.44          | (m1_subset_1 @ 
% 28.26/28.44             (k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X1 @ 
% 28.26/28.44              X0 @ X2) @ 
% 28.26/28.44             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 28.26/28.44          | ~ (v1_relat_1 @ X0)
% 28.26/28.44          | ~ (v1_funct_1 @ X0))),
% 28.26/28.44      inference('simplify', [status(thm)], ['76'])).
% 28.26/28.44  thf('78', plain,
% 28.26/28.44      (![X0 : $i, X1 : $i]:
% 28.26/28.44         (~ (v1_funct_1 @ X0)
% 28.26/28.44          | ~ (v1_relat_1 @ X0)
% 28.26/28.44          | ~ (v1_funct_1 @ X1)
% 28.26/28.44          | ~ (v1_relat_1 @ X1)
% 28.26/28.44          | (m1_subset_1 @ 
% 28.26/28.44             (k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 28.26/28.44              (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0) @ 
% 28.26/28.44             (k1_zfmisc_1 @ 
% 28.26/28.44              (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 28.26/28.44          | ~ (v1_funct_1 @ X0))),
% 28.26/28.44      inference('sup-', [status(thm)], ['73', '77'])).
% 28.26/28.44  thf('79', plain,
% 28.26/28.44      (![X0 : $i, X1 : $i]:
% 28.26/28.44         ((m1_subset_1 @ 
% 28.26/28.44           (k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 28.26/28.44            (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0) @ 
% 28.26/28.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 28.26/28.44          | ~ (v1_relat_1 @ X1)
% 28.26/28.44          | ~ (v1_funct_1 @ X1)
% 28.26/28.44          | ~ (v1_relat_1 @ X0)
% 28.26/28.44          | ~ (v1_funct_1 @ X0))),
% 28.26/28.44      inference('simplify', [status(thm)], ['78'])).
% 28.26/28.44  thf('80', plain,
% 28.26/28.44      (![X0 : $i, X1 : $i]:
% 28.26/28.44         ((m1_subset_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 28.26/28.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 28.26/28.44          | ~ (v1_funct_1 @ X0)
% 28.26/28.44          | ~ (v1_relat_1 @ X0)
% 28.26/28.44          | ~ (v1_funct_1 @ X1)
% 28.26/28.44          | ~ (v1_relat_1 @ X1)
% 28.26/28.44          | ~ (v1_funct_1 @ X0)
% 28.26/28.44          | ~ (v1_relat_1 @ X0)
% 28.26/28.44          | ~ (v1_funct_1 @ X1)
% 28.26/28.44          | ~ (v1_relat_1 @ X1))),
% 28.26/28.44      inference('sup+', [status(thm)], ['72', '79'])).
% 28.26/28.44  thf('81', plain,
% 28.26/28.44      (![X0 : $i, X1 : $i]:
% 28.26/28.44         (~ (v1_relat_1 @ X1)
% 28.26/28.44          | ~ (v1_funct_1 @ X1)
% 28.26/28.44          | ~ (v1_relat_1 @ X0)
% 28.26/28.44          | ~ (v1_funct_1 @ X0)
% 28.26/28.44          | (m1_subset_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 28.26/28.44             (k1_zfmisc_1 @ 
% 28.26/28.44              (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0)))))),
% 28.26/28.44      inference('simplify', [status(thm)], ['80'])).
% 28.26/28.44  thf('82', plain,
% 28.26/28.44      (![X3 : $i, X4 : $i]:
% 28.26/28.44         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 28.26/28.44          | (v1_relat_1 @ X3)
% 28.26/28.44          | ~ (v1_relat_1 @ X4))),
% 28.26/28.44      inference('cnf', [status(esa)], [cc2_relat_1])).
% 28.26/28.44  thf('83', plain,
% 28.26/28.44      (![X0 : $i, X1 : $i]:
% 28.26/28.44         (~ (v1_funct_1 @ X0)
% 28.26/28.44          | ~ (v1_relat_1 @ X0)
% 28.26/28.44          | ~ (v1_funct_1 @ X1)
% 28.26/28.44          | ~ (v1_relat_1 @ X1)
% 28.26/28.44          | ~ (v1_relat_1 @ 
% 28.26/28.44               (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0)))
% 28.26/28.44          | (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 28.26/28.44      inference('sup-', [status(thm)], ['81', '82'])).
% 28.26/28.44  thf('84', plain,
% 28.26/28.44      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 28.26/28.44      inference('cnf', [status(esa)], [fc6_relat_1])).
% 28.26/28.44  thf('85', plain,
% 28.26/28.44      (![X0 : $i, X1 : $i]:
% 28.26/28.44         (~ (v1_funct_1 @ X0)
% 28.26/28.44          | ~ (v1_relat_1 @ X0)
% 28.26/28.44          | ~ (v1_funct_1 @ X1)
% 28.26/28.44          | ~ (v1_relat_1 @ X1)
% 28.26/28.44          | (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 28.26/28.44      inference('demod', [status(thm)], ['83', '84'])).
% 28.26/28.44  thf('86', plain,
% 28.26/28.44      (![X0 : $i, X1 : $i]:
% 28.26/28.44         (~ (v1_relat_1 @ X1)
% 28.26/28.44          | ~ (v1_funct_1 @ X1)
% 28.26/28.44          | ~ (v1_relat_1 @ X0)
% 28.26/28.44          | ~ (v1_funct_1 @ X0)
% 28.26/28.44          | (m1_subset_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 28.26/28.44             (k1_zfmisc_1 @ 
% 28.26/28.44              (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0)))))),
% 28.26/28.44      inference('simplify', [status(thm)], ['80'])).
% 28.26/28.44  thf('87', plain,
% 28.26/28.44      (![X11 : $i, X12 : $i, X13 : $i]:
% 28.26/28.44         ((v5_relat_1 @ X11 @ X13)
% 28.26/28.44          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 28.26/28.44      inference('cnf', [status(esa)], [cc2_relset_1])).
% 28.26/28.44  thf('88', plain,
% 28.26/28.44      (![X0 : $i, X1 : $i]:
% 28.26/28.44         (~ (v1_funct_1 @ X0)
% 28.26/28.44          | ~ (v1_relat_1 @ X0)
% 28.26/28.44          | ~ (v1_funct_1 @ X1)
% 28.26/28.44          | ~ (v1_relat_1 @ X1)
% 28.26/28.44          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 28.26/28.44      inference('sup-', [status(thm)], ['86', '87'])).
% 28.26/28.44  thf('89', plain,
% 28.26/28.44      (![X5 : $i, X6 : $i]:
% 28.26/28.44         (~ (v5_relat_1 @ X5 @ X6)
% 28.26/28.44          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 28.26/28.44          | ~ (v1_relat_1 @ X5))),
% 28.26/28.44      inference('cnf', [status(esa)], [d19_relat_1])).
% 28.26/28.44  thf('90', plain,
% 28.26/28.44      (![X0 : $i, X1 : $i]:
% 28.26/28.44         (~ (v1_relat_1 @ X1)
% 28.26/28.44          | ~ (v1_funct_1 @ X1)
% 28.26/28.44          | ~ (v1_relat_1 @ X0)
% 28.26/28.44          | ~ (v1_funct_1 @ X0)
% 28.26/28.44          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 28.26/28.44          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 28.26/28.44             (k2_relat_1 @ X0)))),
% 28.26/28.44      inference('sup-', [status(thm)], ['88', '89'])).
% 28.26/28.44  thf('91', plain,
% 28.26/28.44      (![X0 : $i, X1 : $i]:
% 28.26/28.44         (~ (v1_relat_1 @ X1)
% 28.26/28.44          | ~ (v1_funct_1 @ X1)
% 28.26/28.44          | ~ (v1_relat_1 @ X0)
% 28.26/28.44          | ~ (v1_funct_1 @ X0)
% 28.26/28.44          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 28.26/28.44             (k2_relat_1 @ X0))
% 28.26/28.44          | ~ (v1_funct_1 @ X0)
% 28.26/28.44          | ~ (v1_relat_1 @ X0)
% 28.26/28.44          | ~ (v1_funct_1 @ X1)
% 28.26/28.44          | ~ (v1_relat_1 @ X1))),
% 28.26/28.44      inference('sup-', [status(thm)], ['85', '90'])).
% 28.26/28.44  thf('92', plain,
% 28.26/28.44      (![X0 : $i, X1 : $i]:
% 28.26/28.44         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 28.26/28.44           (k2_relat_1 @ X0))
% 28.26/28.44          | ~ (v1_funct_1 @ X0)
% 28.26/28.44          | ~ (v1_relat_1 @ X0)
% 28.26/28.44          | ~ (v1_funct_1 @ X1)
% 28.26/28.44          | ~ (v1_relat_1 @ X1))),
% 28.26/28.44      inference('simplify', [status(thm)], ['91'])).
% 28.26/28.44  thf('93', plain,
% 28.26/28.44      (![X0 : $i, X2 : $i]:
% 28.26/28.44         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 28.26/28.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 28.26/28.44  thf('94', plain,
% 28.26/28.44      (![X0 : $i, X1 : $i]:
% 28.26/28.44         (~ (v1_relat_1 @ X1)
% 28.26/28.44          | ~ (v1_funct_1 @ X1)
% 28.26/28.44          | ~ (v1_relat_1 @ X0)
% 28.26/28.44          | ~ (v1_funct_1 @ X0)
% 28.26/28.44          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 28.26/28.44               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 28.26/28.44          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 28.26/28.44      inference('sup-', [status(thm)], ['92', '93'])).
% 28.26/28.44  thf('95', plain,
% 28.26/28.44      ((~ (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)
% 28.26/28.44        | ((k2_relat_1 @ sk_E) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 28.26/28.44        | ~ (v1_funct_1 @ sk_E)
% 28.26/28.44        | ~ (v1_relat_1 @ sk_E)
% 28.26/28.44        | ~ (v1_funct_1 @ sk_D)
% 28.26/28.44        | ~ (v1_relat_1 @ sk_D))),
% 28.26/28.44      inference('sup-', [status(thm)], ['62', '94'])).
% 28.26/28.44  thf('96', plain,
% 28.26/28.44      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 28.26/28.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.44  thf('97', plain,
% 28.26/28.44      (![X11 : $i, X12 : $i, X13 : $i]:
% 28.26/28.44         ((v5_relat_1 @ X11 @ X13)
% 28.26/28.44          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 28.26/28.44      inference('cnf', [status(esa)], [cc2_relset_1])).
% 28.26/28.44  thf('98', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 28.26/28.44      inference('sup-', [status(thm)], ['96', '97'])).
% 28.26/28.44  thf('99', plain,
% 28.26/28.44      (![X5 : $i, X6 : $i]:
% 28.26/28.44         (~ (v5_relat_1 @ X5 @ X6)
% 28.26/28.44          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 28.26/28.44          | ~ (v1_relat_1 @ X5))),
% 28.26/28.44      inference('cnf', [status(esa)], [d19_relat_1])).
% 28.26/28.44  thf('100', plain,
% 28.26/28.44      ((~ (v1_relat_1 @ sk_E) | (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C))),
% 28.26/28.44      inference('sup-', [status(thm)], ['98', '99'])).
% 28.26/28.44  thf('101', plain, ((v1_relat_1 @ sk_E)),
% 28.26/28.44      inference('demod', [status(thm)], ['40', '41'])).
% 28.26/28.44  thf('102', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 28.26/28.44      inference('demod', [status(thm)], ['100', '101'])).
% 28.26/28.44  thf('103', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 28.26/28.44      inference('demod', [status(thm)], ['25', '34'])).
% 28.26/28.44  thf('104', plain, ((v1_funct_1 @ sk_E)),
% 28.26/28.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.44  thf('105', plain, ((v1_relat_1 @ sk_E)),
% 28.26/28.44      inference('demod', [status(thm)], ['40', '41'])).
% 28.26/28.44  thf('106', plain, ((v1_funct_1 @ sk_D)),
% 28.26/28.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.44  thf('107', plain, ((v1_relat_1 @ sk_D)),
% 28.26/28.44      inference('demod', [status(thm)], ['7', '8'])).
% 28.26/28.44  thf('108', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 28.26/28.44      inference('demod', [status(thm)],
% 28.26/28.44                ['95', '102', '103', '104', '105', '106', '107'])).
% 28.26/28.44  thf('109', plain,
% 28.26/28.44      ((((sk_C) != (sk_C)) | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D)))),
% 28.26/28.44      inference('demod', [status(thm)], ['61', '108'])).
% 28.26/28.44  thf('110', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))),
% 28.26/28.44      inference('simplify', [status(thm)], ['109'])).
% 28.26/28.44  thf('111', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 28.26/28.44      inference('demod', [status(thm)], ['12', '110'])).
% 28.26/28.44  thf('112', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 28.26/28.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.44  thf('113', plain,
% 28.26/28.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 28.26/28.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.26/28.44  thf('114', plain,
% 28.26/28.44      (![X17 : $i, X18 : $i, X19 : $i]:
% 28.26/28.44         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 28.26/28.44          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 28.26/28.44      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 28.26/28.44  thf('115', plain,
% 28.26/28.44      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 28.26/28.44      inference('sup-', [status(thm)], ['113', '114'])).
% 28.26/28.44  thf('116', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 28.26/28.44      inference('demod', [status(thm)], ['112', '115'])).
% 28.26/28.44  thf('117', plain, ($false),
% 28.26/28.44      inference('simplify_reflect-', [status(thm)], ['111', '116'])).
% 28.26/28.44  
% 28.26/28.44  % SZS output end Refutation
% 28.26/28.44  
% 28.28/28.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UNMrp6BNM1

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:56 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 332 expanded)
%              Number of leaves         :   41 ( 114 expanded)
%              Depth                    :   15
%              Number of atoms          : 1025 (7395 expanded)
%              Number of equality atoms :   59 ( 430 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['4','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 )
        = ( k5_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['17','18','27'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('33',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['30','33'])).

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

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X11 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X11 @ X12 ) )
       != ( k2_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t51_funct_1])).

thf('36',plain,
    ( ( sk_C
     != ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E )
    | ( r1_tarski @ ( k1_relat_1 @ sk_E ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
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

thf('43',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('44',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('45',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('48',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('53',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('54',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['44','51','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('58',plain,
    ( ( sk_C
     != ( k2_relat_1 @ sk_E ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['36','39','40','41','55','56','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['30','33'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('60',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) ) @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('61',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C )
    | ( ( k2_relat_1 @ sk_E )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('66',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['37','38'])).

thf('70',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['30','33'])).

thf('72',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['37','38'])).

thf('73',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['63','70','71','72','73'])).

thf('75',plain,
    ( ( sk_C != sk_C )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['58','74'])).

thf('76',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['10','76'])).

thf('78',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('81',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['77','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UNMrp6BNM1
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 18:56:22 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  % Running portfolio for 600 s
% 0.15/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.34  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 1.53/1.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.53/1.74  % Solved by: fo/fo7.sh
% 1.53/1.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.53/1.74  % done 712 iterations in 1.272s
% 1.53/1.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.53/1.74  % SZS output start Refutation
% 1.53/1.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.53/1.74  thf(sk_D_type, type, sk_D: $i).
% 1.53/1.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.53/1.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.53/1.74  thf(sk_A_type, type, sk_A: $i).
% 1.53/1.74  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.53/1.74  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.53/1.74  thf(sk_C_type, type, sk_C: $i).
% 1.53/1.74  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.53/1.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.53/1.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.53/1.74  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.53/1.74  thf(sk_E_type, type, sk_E: $i).
% 1.53/1.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.53/1.74  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.53/1.74  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.53/1.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.53/1.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.53/1.74  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.53/1.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.53/1.74  thf(sk_B_type, type, sk_B: $i).
% 1.53/1.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.53/1.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.53/1.74  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.53/1.74  thf(t28_funct_2, conjecture,
% 1.53/1.74    (![A:$i,B:$i,C:$i,D:$i]:
% 1.53/1.74     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.53/1.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.53/1.74       ( ![E:$i]:
% 1.53/1.74         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.53/1.74             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.53/1.74           ( ( ( ( k2_relset_1 @
% 1.53/1.74                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.53/1.74                 ( C ) ) & 
% 1.53/1.74               ( v2_funct_1 @ E ) ) =>
% 1.53/1.74             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.53/1.74               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 1.53/1.74  thf(zf_stmt_0, negated_conjecture,
% 1.53/1.74    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.53/1.74        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.53/1.74            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.53/1.74          ( ![E:$i]:
% 1.53/1.74            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.53/1.74                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.53/1.74              ( ( ( ( k2_relset_1 @
% 1.53/1.74                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.53/1.74                    ( C ) ) & 
% 1.53/1.74                  ( v2_funct_1 @ E ) ) =>
% 1.53/1.74                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.53/1.74                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 1.53/1.74    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 1.53/1.74  thf('0', plain,
% 1.53/1.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.74  thf(cc2_relset_1, axiom,
% 1.53/1.74    (![A:$i,B:$i,C:$i]:
% 1.53/1.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.53/1.74       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.53/1.74  thf('1', plain,
% 1.53/1.74      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.53/1.74         ((v5_relat_1 @ X16 @ X18)
% 1.53/1.74          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.53/1.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.53/1.74  thf('2', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 1.53/1.74      inference('sup-', [status(thm)], ['0', '1'])).
% 1.53/1.74  thf(d19_relat_1, axiom,
% 1.53/1.74    (![A:$i,B:$i]:
% 1.53/1.74     ( ( v1_relat_1 @ B ) =>
% 1.53/1.74       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.53/1.74  thf('3', plain,
% 1.53/1.74      (![X3 : $i, X4 : $i]:
% 1.53/1.74         (~ (v5_relat_1 @ X3 @ X4)
% 1.53/1.74          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 1.53/1.74          | ~ (v1_relat_1 @ X3))),
% 1.53/1.74      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.53/1.74  thf('4', plain,
% 1.53/1.74      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 1.53/1.74      inference('sup-', [status(thm)], ['2', '3'])).
% 1.53/1.74  thf('5', plain,
% 1.53/1.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.74  thf(cc1_relset_1, axiom,
% 1.53/1.74    (![A:$i,B:$i,C:$i]:
% 1.53/1.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.53/1.74       ( v1_relat_1 @ C ) ))).
% 1.53/1.74  thf('6', plain,
% 1.53/1.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.53/1.74         ((v1_relat_1 @ X13)
% 1.53/1.74          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.53/1.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.53/1.74  thf('7', plain, ((v1_relat_1 @ sk_D)),
% 1.53/1.74      inference('sup-', [status(thm)], ['5', '6'])).
% 1.53/1.74  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 1.53/1.74      inference('demod', [status(thm)], ['4', '7'])).
% 1.53/1.74  thf(d10_xboole_0, axiom,
% 1.53/1.74    (![A:$i,B:$i]:
% 1.53/1.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.53/1.74  thf('9', plain,
% 1.53/1.74      (![X0 : $i, X2 : $i]:
% 1.53/1.74         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.53/1.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.53/1.74  thf('10', plain,
% 1.53/1.74      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))
% 1.53/1.74        | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 1.53/1.74      inference('sup-', [status(thm)], ['8', '9'])).
% 1.53/1.74  thf('11', plain,
% 1.53/1.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.74  thf('12', plain,
% 1.53/1.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.74  thf(dt_k1_partfun1, axiom,
% 1.53/1.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.53/1.74     ( ( ( v1_funct_1 @ E ) & 
% 1.53/1.74         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.53/1.74         ( v1_funct_1 @ F ) & 
% 1.53/1.74         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.53/1.74       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.53/1.74         ( m1_subset_1 @
% 1.53/1.74           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.53/1.74           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.53/1.74  thf('13', plain,
% 1.53/1.74      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.53/1.74         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.53/1.74          | ~ (v1_funct_1 @ X33)
% 1.53/1.74          | ~ (v1_funct_1 @ X36)
% 1.53/1.74          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.53/1.74          | (m1_subset_1 @ (k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36) @ 
% 1.53/1.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X38))))),
% 1.53/1.74      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.53/1.74  thf('14', plain,
% 1.53/1.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.74         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 1.53/1.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.53/1.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.53/1.74          | ~ (v1_funct_1 @ X1)
% 1.53/1.74          | ~ (v1_funct_1 @ sk_D))),
% 1.53/1.74      inference('sup-', [status(thm)], ['12', '13'])).
% 1.53/1.74  thf('15', plain, ((v1_funct_1 @ sk_D)),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.74  thf('16', plain,
% 1.53/1.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.74         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 1.53/1.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.53/1.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.53/1.74          | ~ (v1_funct_1 @ X1))),
% 1.53/1.74      inference('demod', [status(thm)], ['14', '15'])).
% 1.53/1.74  thf('17', plain,
% 1.53/1.74      ((~ (v1_funct_1 @ sk_E)
% 1.53/1.74        | (m1_subset_1 @ 
% 1.53/1.74           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 1.53/1.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.53/1.74      inference('sup-', [status(thm)], ['11', '16'])).
% 1.53/1.74  thf('18', plain, ((v1_funct_1 @ sk_E)),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.74  thf('19', plain,
% 1.53/1.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.74  thf('20', plain,
% 1.53/1.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.74  thf(redefinition_k1_partfun1, axiom,
% 1.53/1.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.53/1.74     ( ( ( v1_funct_1 @ E ) & 
% 1.53/1.74         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.53/1.74         ( v1_funct_1 @ F ) & 
% 1.53/1.74         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.53/1.74       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.53/1.74  thf('21', plain,
% 1.53/1.74      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.53/1.74         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 1.53/1.74          | ~ (v1_funct_1 @ X39)
% 1.53/1.74          | ~ (v1_funct_1 @ X42)
% 1.53/1.74          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 1.53/1.74          | ((k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42)
% 1.53/1.74              = (k5_relat_1 @ X39 @ X42)))),
% 1.53/1.74      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.53/1.74  thf('22', plain,
% 1.53/1.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.74         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.53/1.74            = (k5_relat_1 @ sk_D @ X0))
% 1.53/1.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.53/1.74          | ~ (v1_funct_1 @ X0)
% 1.53/1.74          | ~ (v1_funct_1 @ sk_D))),
% 1.53/1.74      inference('sup-', [status(thm)], ['20', '21'])).
% 1.53/1.74  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.74  thf('24', plain,
% 1.53/1.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.74         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.53/1.74            = (k5_relat_1 @ sk_D @ X0))
% 1.53/1.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.53/1.74          | ~ (v1_funct_1 @ X0))),
% 1.53/1.74      inference('demod', [status(thm)], ['22', '23'])).
% 1.53/1.74  thf('25', plain,
% 1.53/1.74      ((~ (v1_funct_1 @ sk_E)
% 1.53/1.74        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.53/1.74            = (k5_relat_1 @ sk_D @ sk_E)))),
% 1.53/1.74      inference('sup-', [status(thm)], ['19', '24'])).
% 1.53/1.74  thf('26', plain, ((v1_funct_1 @ sk_E)),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.74  thf('27', plain,
% 1.53/1.74      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.53/1.74         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.53/1.74      inference('demod', [status(thm)], ['25', '26'])).
% 1.53/1.74  thf('28', plain,
% 1.53/1.74      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 1.53/1.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.53/1.74      inference('demod', [status(thm)], ['17', '18', '27'])).
% 1.53/1.74  thf(redefinition_k2_relset_1, axiom,
% 1.53/1.74    (![A:$i,B:$i,C:$i]:
% 1.53/1.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.53/1.74       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.53/1.74  thf('29', plain,
% 1.53/1.74      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.53/1.74         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 1.53/1.74          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.53/1.74      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.53/1.74  thf('30', plain,
% 1.53/1.74      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 1.53/1.74         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 1.53/1.74      inference('sup-', [status(thm)], ['28', '29'])).
% 1.53/1.74  thf('31', plain,
% 1.53/1.74      (((k2_relset_1 @ sk_A @ sk_C @ 
% 1.53/1.74         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.74  thf('32', plain,
% 1.53/1.74      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.53/1.74         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.53/1.74      inference('demod', [status(thm)], ['25', '26'])).
% 1.53/1.74  thf('33', plain,
% 1.53/1.74      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.53/1.74      inference('demod', [status(thm)], ['31', '32'])).
% 1.53/1.74  thf('34', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.53/1.74      inference('sup+', [status(thm)], ['30', '33'])).
% 1.53/1.74  thf(t51_funct_1, axiom,
% 1.53/1.74    (![A:$i]:
% 1.53/1.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.53/1.74       ( ![B:$i]:
% 1.53/1.74         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.53/1.74           ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) & 
% 1.53/1.74               ( v2_funct_1 @ A ) ) =>
% 1.53/1.74             ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 1.53/1.74  thf('35', plain,
% 1.53/1.74      (![X11 : $i, X12 : $i]:
% 1.53/1.74         (~ (v1_relat_1 @ X11)
% 1.53/1.74          | ~ (v1_funct_1 @ X11)
% 1.53/1.74          | (r1_tarski @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X11))
% 1.53/1.74          | ((k2_relat_1 @ (k5_relat_1 @ X11 @ X12)) != (k2_relat_1 @ X12))
% 1.53/1.74          | ~ (v2_funct_1 @ X12)
% 1.53/1.74          | ~ (v1_funct_1 @ X12)
% 1.53/1.74          | ~ (v1_relat_1 @ X12))),
% 1.53/1.74      inference('cnf', [status(esa)], [t51_funct_1])).
% 1.53/1.74  thf('36', plain,
% 1.53/1.74      ((((sk_C) != (k2_relat_1 @ sk_E))
% 1.53/1.74        | ~ (v1_relat_1 @ sk_E)
% 1.53/1.74        | ~ (v1_funct_1 @ sk_E)
% 1.53/1.74        | ~ (v2_funct_1 @ sk_E)
% 1.53/1.74        | (r1_tarski @ (k1_relat_1 @ sk_E) @ (k2_relat_1 @ sk_D))
% 1.53/1.74        | ~ (v1_funct_1 @ sk_D)
% 1.53/1.74        | ~ (v1_relat_1 @ sk_D))),
% 1.53/1.74      inference('sup-', [status(thm)], ['34', '35'])).
% 1.53/1.74  thf('37', plain,
% 1.53/1.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.74  thf('38', plain,
% 1.53/1.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.53/1.74         ((v1_relat_1 @ X13)
% 1.53/1.74          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.53/1.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.53/1.74  thf('39', plain, ((v1_relat_1 @ sk_E)),
% 1.53/1.74      inference('sup-', [status(thm)], ['37', '38'])).
% 1.53/1.74  thf('40', plain, ((v1_funct_1 @ sk_E)),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.74  thf('41', plain, ((v2_funct_1 @ sk_E)),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.74  thf('42', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.74  thf(d1_funct_2, axiom,
% 1.53/1.74    (![A:$i,B:$i,C:$i]:
% 1.53/1.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.53/1.74       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.53/1.74           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.53/1.74             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.53/1.74         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.53/1.74           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.53/1.74             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.53/1.74  thf(zf_stmt_1, axiom,
% 1.53/1.74    (![C:$i,B:$i,A:$i]:
% 1.53/1.74     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.53/1.74       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.53/1.74  thf('43', plain,
% 1.53/1.74      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.53/1.74         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 1.53/1.74          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 1.53/1.74          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.53/1.74  thf('44', plain,
% 1.53/1.74      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 1.53/1.74        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 1.53/1.74      inference('sup-', [status(thm)], ['42', '43'])).
% 1.53/1.74  thf(zf_stmt_2, axiom,
% 1.53/1.74    (![B:$i,A:$i]:
% 1.53/1.74     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.53/1.74       ( zip_tseitin_0 @ B @ A ) ))).
% 1.53/1.74  thf('45', plain,
% 1.53/1.74      (![X25 : $i, X26 : $i]:
% 1.53/1.74         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.53/1.74  thf('46', plain,
% 1.53/1.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.74  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.53/1.74  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.53/1.74  thf(zf_stmt_5, axiom,
% 1.53/1.74    (![A:$i,B:$i,C:$i]:
% 1.53/1.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.53/1.74       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.53/1.74         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.53/1.74           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.53/1.74             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.53/1.74  thf('47', plain,
% 1.53/1.74      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.53/1.74         (~ (zip_tseitin_0 @ X30 @ X31)
% 1.53/1.74          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 1.53/1.74          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.53/1.74  thf('48', plain,
% 1.53/1.74      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.53/1.74      inference('sup-', [status(thm)], ['46', '47'])).
% 1.53/1.74  thf('49', plain,
% 1.53/1.74      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 1.53/1.74      inference('sup-', [status(thm)], ['45', '48'])).
% 1.53/1.74  thf('50', plain, (((sk_C) != (k1_xboole_0))),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.74  thf('51', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 1.53/1.74      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 1.53/1.74  thf('52', plain,
% 1.53/1.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.74  thf(redefinition_k1_relset_1, axiom,
% 1.53/1.74    (![A:$i,B:$i,C:$i]:
% 1.53/1.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.53/1.74       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.53/1.74  thf('53', plain,
% 1.53/1.74      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.53/1.74         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 1.53/1.74          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.53/1.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.53/1.74  thf('54', plain,
% 1.53/1.74      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.53/1.74      inference('sup-', [status(thm)], ['52', '53'])).
% 1.53/1.74  thf('55', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 1.53/1.74      inference('demod', [status(thm)], ['44', '51', '54'])).
% 1.53/1.74  thf('56', plain, ((v1_funct_1 @ sk_D)),
% 1.53/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.74  thf('57', plain, ((v1_relat_1 @ sk_D)),
% 1.53/1.74      inference('sup-', [status(thm)], ['5', '6'])).
% 1.53/1.74  thf('58', plain,
% 1.53/1.74      ((((sk_C) != (k2_relat_1 @ sk_E))
% 1.53/1.74        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D)))),
% 1.53/1.74      inference('demod', [status(thm)],
% 1.53/1.74                ['36', '39', '40', '41', '55', '56', '57'])).
% 1.53/1.74  thf('59', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.53/1.74      inference('sup+', [status(thm)], ['30', '33'])).
% 1.53/1.74  thf(t45_relat_1, axiom,
% 1.53/1.74    (![A:$i]:
% 1.53/1.74     ( ( v1_relat_1 @ A ) =>
% 1.53/1.74       ( ![B:$i]:
% 1.53/1.74         ( ( v1_relat_1 @ B ) =>
% 1.53/1.74           ( r1_tarski @
% 1.53/1.74             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 1.53/1.75  thf('60', plain,
% 1.53/1.75      (![X9 : $i, X10 : $i]:
% 1.53/1.75         (~ (v1_relat_1 @ X9)
% 1.53/1.75          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X10 @ X9)) @ 
% 1.53/1.75             (k2_relat_1 @ X9))
% 1.53/1.75          | ~ (v1_relat_1 @ X10))),
% 1.53/1.75      inference('cnf', [status(esa)], [t45_relat_1])).
% 1.53/1.75  thf('61', plain,
% 1.53/1.75      (![X0 : $i, X2 : $i]:
% 1.53/1.75         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.53/1.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.53/1.75  thf('62', plain,
% 1.53/1.75      (![X0 : $i, X1 : $i]:
% 1.53/1.75         (~ (v1_relat_1 @ X1)
% 1.53/1.75          | ~ (v1_relat_1 @ X0)
% 1.53/1.75          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 1.53/1.75               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 1.53/1.75          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 1.53/1.75      inference('sup-', [status(thm)], ['60', '61'])).
% 1.53/1.75  thf('63', plain,
% 1.53/1.75      ((~ (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)
% 1.53/1.75        | ((k2_relat_1 @ sk_E) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 1.53/1.75        | ~ (v1_relat_1 @ sk_E)
% 1.53/1.75        | ~ (v1_relat_1 @ sk_D))),
% 1.53/1.75      inference('sup-', [status(thm)], ['59', '62'])).
% 1.53/1.75  thf('64', plain,
% 1.53/1.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.53/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.75  thf('65', plain,
% 1.53/1.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.53/1.75         ((v5_relat_1 @ X16 @ X18)
% 1.53/1.75          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.53/1.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.53/1.75  thf('66', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 1.53/1.75      inference('sup-', [status(thm)], ['64', '65'])).
% 1.53/1.75  thf('67', plain,
% 1.53/1.75      (![X3 : $i, X4 : $i]:
% 1.53/1.75         (~ (v5_relat_1 @ X3 @ X4)
% 1.53/1.75          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 1.53/1.75          | ~ (v1_relat_1 @ X3))),
% 1.53/1.75      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.53/1.75  thf('68', plain,
% 1.53/1.75      ((~ (v1_relat_1 @ sk_E) | (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C))),
% 1.53/1.75      inference('sup-', [status(thm)], ['66', '67'])).
% 1.53/1.75  thf('69', plain, ((v1_relat_1 @ sk_E)),
% 1.53/1.75      inference('sup-', [status(thm)], ['37', '38'])).
% 1.53/1.75  thf('70', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 1.53/1.75      inference('demod', [status(thm)], ['68', '69'])).
% 1.53/1.75  thf('71', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.53/1.75      inference('sup+', [status(thm)], ['30', '33'])).
% 1.53/1.75  thf('72', plain, ((v1_relat_1 @ sk_E)),
% 1.53/1.75      inference('sup-', [status(thm)], ['37', '38'])).
% 1.53/1.75  thf('73', plain, ((v1_relat_1 @ sk_D)),
% 1.53/1.75      inference('sup-', [status(thm)], ['5', '6'])).
% 1.53/1.75  thf('74', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 1.53/1.75      inference('demod', [status(thm)], ['63', '70', '71', '72', '73'])).
% 1.53/1.75  thf('75', plain,
% 1.53/1.75      ((((sk_C) != (sk_C)) | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D)))),
% 1.53/1.75      inference('demod', [status(thm)], ['58', '74'])).
% 1.53/1.75  thf('76', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))),
% 1.53/1.75      inference('simplify', [status(thm)], ['75'])).
% 1.53/1.75  thf('77', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 1.53/1.75      inference('demod', [status(thm)], ['10', '76'])).
% 1.53/1.75  thf('78', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 1.53/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.75  thf('79', plain,
% 1.53/1.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.53/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.75  thf('80', plain,
% 1.53/1.75      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.53/1.75         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 1.53/1.75          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.53/1.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.53/1.75  thf('81', plain,
% 1.53/1.75      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.53/1.75      inference('sup-', [status(thm)], ['79', '80'])).
% 1.53/1.75  thf('82', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 1.53/1.75      inference('demod', [status(thm)], ['78', '81'])).
% 1.53/1.75  thf('83', plain, ($false),
% 1.53/1.75      inference('simplify_reflect-', [status(thm)], ['77', '82'])).
% 1.53/1.75  
% 1.53/1.75  % SZS output end Refutation
% 1.53/1.75  
% 1.53/1.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

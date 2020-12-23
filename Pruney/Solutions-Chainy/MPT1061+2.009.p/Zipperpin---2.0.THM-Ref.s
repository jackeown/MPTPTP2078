%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dyjJSXaDiI

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:53 EST 2020

% Result     : Theorem 13.66s
% Output     : Refutation 13.66s
% Verified   : 
% Statistics : Number of formulae       :  254 (1799 expanded)
%              Number of leaves         :   52 ( 555 expanded)
%              Depth                    :   27
%              Number of atoms          : 1804 (22943 expanded)
%              Number of equality atoms :   95 ( 712 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t178_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ~ ( v1_xboole_0 @ D )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ A @ D )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) )
         => ( ( ( r1_tarski @ B @ A )
              & ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) )
           => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) )
              & ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C )
              & ( m1_subset_1 @ ( k2_partfun1 @ A @ D @ E @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ~ ( v1_xboole_0 @ D )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ A @ D )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) )
           => ( ( ( r1_tarski @ B @ A )
                & ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) )
             => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) )
                & ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C )
                & ( m1_subset_1 @ ( k2_partfun1 @ A @ D @ E @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t178_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ~ ( v1_funct_1 @ X54 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X55 @ X56 @ X54 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('8',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) )
      | ~ ( v1_funct_1 @ X58 )
      | ( ( k2_partfun1 @ X59 @ X60 @ X58 @ X61 )
        = ( k7_relat_1 @ X58 @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('13',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['6','11','12'])).

thf('14',plain,(
    r1_tarski @ ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('16',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k7_relset_1 @ X40 @ X41 @ X39 @ X42 )
        = ( k9_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_E @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['14','17'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) )
        = ( k9_relat_1 @ X24 @ X25 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ( v5_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v5_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ~ ( v1_funct_1 @ X54 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X55 @ X56 @ X54 @ X57 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('30',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v5_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['22','31','34'])).

thf('36',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v5_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('39',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ sk_C_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('42',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X43 ) @ X44 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X43 ) @ X45 )
      | ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_D ),
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

thf('47',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( v1_funct_2 @ X50 @ X48 @ X49 )
      | ( X48
        = ( k1_relset_1 @ X48 @ X49 @ X50 ) )
      | ~ ( zip_tseitin_1 @ X50 @ X49 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('48',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('50',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k1_relset_1 @ X37 @ X38 @ X36 )
        = ( k1_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('51',plain,
    ( ( k1_relset_1 @ sk_A @ sk_D @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( zip_tseitin_0 @ X51 @ X52 )
      | ( zip_tseitin_1 @ X53 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('55',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X46: $i,X47: $i] :
      ( ( zip_tseitin_0 @ X46 @ X47 )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('57',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('58',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['56','58'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('60',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('61',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('62',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('64',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,(
    r1_tarski @ sk_E @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_D ) @ sk_E )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_D )
      = sk_E ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_D )
      = sk_E ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_D )
        = sk_E ) ) ),
    inference('sup-',[status(thm)],['59','72'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_D )
        = sk_E ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('79',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( sk_E = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['75','84'])).

thf('86',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X46: $i,X47: $i] :
      ( ( zip_tseitin_0 @ X46 @ X47 )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_D @ X0 ) ),
    inference(clc,[status(thm)],['87','90'])).

thf('92',plain,(
    zip_tseitin_1 @ sk_E @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['55','91'])).

thf('93',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['52','92'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('94',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X28 @ ( k1_relat_1 @ X29 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X29 @ X28 ) )
        = X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['32','33'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['45','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('100',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['44','98','99'])).

thf('101',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['13','100'])).

thf('102',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['44','98','99'])).

thf('103',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k1_relset_1 @ X37 @ X38 @ X36 )
        = ( k1_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('104',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['45','97'])).

thf('106',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48
       != ( k1_relset_1 @ X48 @ X49 @ X50 ) )
      | ( v1_funct_2 @ X50 @ X48 @ X49 )
      | ~ ( zip_tseitin_1 @ X50 @ X49 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('108',plain,
    ( ( sk_B != sk_B )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C_1 @ sk_B )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C_1 )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['44','98','99'])).

thf('111',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( zip_tseitin_0 @ X51 @ X52 )
      | ( zip_tseitin_1 @ X53 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('112',plain,
    ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C_1 @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['56','58'])).

thf('114',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['44','98','99'])).

thf('115',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('116',plain,(
    r1_tarski @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('118',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('119',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('121',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v5_relat_1 @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( v5_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['119','122'])).

thf('124',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v5_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['118'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('127',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('128',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['125','128'])).

thf('130',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( v5_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('132',plain,(
    v5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v5_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('134',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['126','127'])).

thf('136',plain,(
    r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('138',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('140',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['129','140'])).

thf('142',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['117','143'])).

thf('145',plain,
    ( ( ( k7_relat_1 @ sk_E @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['116','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X0 )
      | ( ( k7_relat_1 @ sk_E @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['113','145'])).

thf('147',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C_1 @ X0 )
      | ( ( k7_relat_1 @ sk_E @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('151',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['129','140'])).

thf('152',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('153',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k1_relset_1 @ X37 @ X38 @ X36 )
        = ( k1_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('157',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('158',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v4_relat_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['156','159'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('161',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['126','127'])).

thf('164',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('166',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['155','166'])).

thf('168',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48
       != ( k1_relset_1 @ X48 @ X49 @ X50 ) )
      | ( v1_funct_2 @ X50 @ X48 @ X49 )
      | ~ ( zip_tseitin_1 @ X50 @ X49 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    ! [X46: $i,X47: $i] :
      ( ( zip_tseitin_0 @ X46 @ X47 )
      | ( X47 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('172',plain,(
    ! [X46: $i] :
      ( zip_tseitin_0 @ X46 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('174',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( zip_tseitin_0 @ X51 @ X52 )
      | ( zip_tseitin_1 @ X53 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['172','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['170','176'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['150','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ X2 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['149','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('181',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['6','11','12'])).

thf('184',plain,
    ( ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,
    ( ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['179','184'])).

thf('186',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['45','97'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('189',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['164','165'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['188','189'])).

thf('191',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['190','191'])).

thf('193',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup+',[status(thm)],['187','192'])).

thf('194',plain,(
    ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference(clc,[status(thm)],['186','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','194'])).

thf('196',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('197',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C_1 @ X0 ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,(
    zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['112','197'])).

thf('199',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['109','198'])).

thf('200',plain,(
    $false ),
    inference(demod,[status(thm)],['101','199'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dyjJSXaDiI
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:02:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 13.66/13.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 13.66/13.89  % Solved by: fo/fo7.sh
% 13.66/13.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.66/13.89  % done 13647 iterations in 13.433s
% 13.66/13.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 13.66/13.89  % SZS output start Refutation
% 13.66/13.89  thf(sk_C_1_type, type, sk_C_1: $i).
% 13.66/13.89  thf(sk_B_type, type, sk_B: $i).
% 13.66/13.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 13.66/13.89  thf(sk_A_type, type, sk_A: $i).
% 13.66/13.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 13.66/13.89  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 13.66/13.89  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 13.66/13.89  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 13.66/13.89  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 13.66/13.89  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 13.66/13.89  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 13.66/13.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 13.66/13.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 13.66/13.89  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 13.66/13.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 13.66/13.89  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 13.66/13.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 13.66/13.89  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 13.66/13.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 13.66/13.89  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 13.66/13.89  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 13.66/13.89  thf(sk_D_type, type, sk_D: $i).
% 13.66/13.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 13.66/13.89  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 13.66/13.89  thf(sk_E_type, type, sk_E: $i).
% 13.66/13.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 13.66/13.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 13.66/13.89  thf(t178_funct_2, conjecture,
% 13.66/13.89    (![A:$i,B:$i,C:$i,D:$i]:
% 13.66/13.89     ( ( ~( v1_xboole_0 @ D ) ) =>
% 13.66/13.89       ( ![E:$i]:
% 13.66/13.89         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 13.66/13.89             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 13.66/13.89           ( ( ( r1_tarski @ B @ A ) & 
% 13.66/13.89               ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 13.66/13.89             ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 13.66/13.89               ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 13.66/13.89               ( m1_subset_1 @
% 13.66/13.89                 ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 13.66/13.89                 ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ))).
% 13.66/13.89  thf(zf_stmt_0, negated_conjecture,
% 13.66/13.89    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 13.66/13.89        ( ( ~( v1_xboole_0 @ D ) ) =>
% 13.66/13.89          ( ![E:$i]:
% 13.66/13.89            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 13.66/13.89                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 13.66/13.89              ( ( ( r1_tarski @ B @ A ) & 
% 13.66/13.89                  ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 13.66/13.89                ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 13.66/13.89                  ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 13.66/13.89                  ( m1_subset_1 @
% 13.66/13.89                    ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 13.66/13.89                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ) )),
% 13.66/13.89    inference('cnf.neg', [status(esa)], [t178_funct_2])).
% 13.66/13.89  thf('0', plain,
% 13.66/13.89      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B))
% 13.66/13.89        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 13.66/13.89             sk_C_1)
% 13.66/13.89        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 13.66/13.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1))))),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.66/13.89  thf('1', plain,
% 13.66/13.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.66/13.89  thf(dt_k2_partfun1, axiom,
% 13.66/13.89    (![A:$i,B:$i,C:$i,D:$i]:
% 13.66/13.89     ( ( ( v1_funct_1 @ C ) & 
% 13.66/13.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 13.66/13.89       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 13.66/13.89         ( m1_subset_1 @
% 13.66/13.89           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 13.66/13.89           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 13.66/13.89  thf('2', plain,
% 13.66/13.89      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 13.66/13.89         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 13.66/13.89          | ~ (v1_funct_1 @ X54)
% 13.66/13.89          | (v1_funct_1 @ (k2_partfun1 @ X55 @ X56 @ X54 @ X57)))),
% 13.66/13.89      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 13.66/13.89  thf('3', plain,
% 13.66/13.89      (![X0 : $i]:
% 13.66/13.89         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))
% 13.66/13.89          | ~ (v1_funct_1 @ sk_E))),
% 13.66/13.89      inference('sup-', [status(thm)], ['1', '2'])).
% 13.66/13.89  thf('4', plain, ((v1_funct_1 @ sk_E)),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.66/13.89  thf('5', plain,
% 13.66/13.89      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 13.66/13.89      inference('demod', [status(thm)], ['3', '4'])).
% 13.66/13.89  thf('6', plain,
% 13.66/13.89      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 13.66/13.89           sk_C_1)
% 13.66/13.89        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 13.66/13.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1))))),
% 13.66/13.89      inference('demod', [status(thm)], ['0', '5'])).
% 13.66/13.89  thf('7', plain,
% 13.66/13.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.66/13.89  thf(redefinition_k2_partfun1, axiom,
% 13.66/13.89    (![A:$i,B:$i,C:$i,D:$i]:
% 13.66/13.89     ( ( ( v1_funct_1 @ C ) & 
% 13.66/13.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 13.66/13.89       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 13.66/13.89  thf('8', plain,
% 13.66/13.89      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 13.66/13.89         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60)))
% 13.66/13.89          | ~ (v1_funct_1 @ X58)
% 13.66/13.89          | ((k2_partfun1 @ X59 @ X60 @ X58 @ X61) = (k7_relat_1 @ X58 @ X61)))),
% 13.66/13.89      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 13.66/13.89  thf('9', plain,
% 13.66/13.89      (![X0 : $i]:
% 13.66/13.89         (((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 13.66/13.89          | ~ (v1_funct_1 @ sk_E))),
% 13.66/13.89      inference('sup-', [status(thm)], ['7', '8'])).
% 13.66/13.89  thf('10', plain, ((v1_funct_1 @ sk_E)),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.66/13.89  thf('11', plain,
% 13.66/13.89      (![X0 : $i]:
% 13.66/13.89         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 13.66/13.89      inference('demod', [status(thm)], ['9', '10'])).
% 13.66/13.89  thf('12', plain,
% 13.66/13.89      (![X0 : $i]:
% 13.66/13.89         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 13.66/13.89      inference('demod', [status(thm)], ['9', '10'])).
% 13.66/13.89  thf('13', plain,
% 13.66/13.89      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C_1)
% 13.66/13.89        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 13.66/13.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1))))),
% 13.66/13.89      inference('demod', [status(thm)], ['6', '11', '12'])).
% 13.66/13.89  thf('14', plain,
% 13.66/13.89      ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_C_1)),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.66/13.89  thf('15', plain,
% 13.66/13.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.66/13.89  thf(redefinition_k7_relset_1, axiom,
% 13.66/13.89    (![A:$i,B:$i,C:$i,D:$i]:
% 13.66/13.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.66/13.89       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 13.66/13.89  thf('16', plain,
% 13.66/13.89      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 13.66/13.89         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 13.66/13.89          | ((k7_relset_1 @ X40 @ X41 @ X39 @ X42) = (k9_relat_1 @ X39 @ X42)))),
% 13.66/13.89      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 13.66/13.89  thf('17', plain,
% 13.66/13.89      (![X0 : $i]:
% 13.66/13.89         ((k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0) = (k9_relat_1 @ sk_E @ X0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['15', '16'])).
% 13.66/13.89  thf('18', plain, ((r1_tarski @ (k9_relat_1 @ sk_E @ sk_B) @ sk_C_1)),
% 13.66/13.89      inference('demod', [status(thm)], ['14', '17'])).
% 13.66/13.89  thf(t148_relat_1, axiom,
% 13.66/13.89    (![A:$i,B:$i]:
% 13.66/13.89     ( ( v1_relat_1 @ B ) =>
% 13.66/13.89       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 13.66/13.89  thf('19', plain,
% 13.66/13.89      (![X24 : $i, X25 : $i]:
% 13.66/13.89         (((k2_relat_1 @ (k7_relat_1 @ X24 @ X25)) = (k9_relat_1 @ X24 @ X25))
% 13.66/13.89          | ~ (v1_relat_1 @ X24))),
% 13.66/13.89      inference('cnf', [status(esa)], [t148_relat_1])).
% 13.66/13.89  thf(d19_relat_1, axiom,
% 13.66/13.89    (![A:$i,B:$i]:
% 13.66/13.89     ( ( v1_relat_1 @ B ) =>
% 13.66/13.89       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 13.66/13.89  thf('20', plain,
% 13.66/13.89      (![X18 : $i, X19 : $i]:
% 13.66/13.89         (~ (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 13.66/13.89          | (v5_relat_1 @ X18 @ X19)
% 13.66/13.89          | ~ (v1_relat_1 @ X18))),
% 13.66/13.89      inference('cnf', [status(esa)], [d19_relat_1])).
% 13.66/13.89  thf('21', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.66/13.89         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 13.66/13.89          | ~ (v1_relat_1 @ X1)
% 13.66/13.89          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 13.66/13.89          | (v5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))),
% 13.66/13.89      inference('sup-', [status(thm)], ['19', '20'])).
% 13.66/13.89  thf('22', plain,
% 13.66/13.89      (((v5_relat_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C_1)
% 13.66/13.89        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 13.66/13.89        | ~ (v1_relat_1 @ sk_E))),
% 13.66/13.89      inference('sup-', [status(thm)], ['18', '21'])).
% 13.66/13.89  thf('23', plain,
% 13.66/13.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.66/13.89  thf('24', plain,
% 13.66/13.89      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 13.66/13.89         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 13.66/13.89          | ~ (v1_funct_1 @ X54)
% 13.66/13.89          | (m1_subset_1 @ (k2_partfun1 @ X55 @ X56 @ X54 @ X57) @ 
% 13.66/13.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56))))),
% 13.66/13.89      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 13.66/13.89  thf('25', plain,
% 13.66/13.89      (![X0 : $i]:
% 13.66/13.89         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 13.66/13.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))
% 13.66/13.89          | ~ (v1_funct_1 @ sk_E))),
% 13.66/13.89      inference('sup-', [status(thm)], ['23', '24'])).
% 13.66/13.89  thf('26', plain, ((v1_funct_1 @ sk_E)),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.66/13.89  thf('27', plain,
% 13.66/13.89      (![X0 : $i]:
% 13.66/13.89         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 13.66/13.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 13.66/13.89      inference('demod', [status(thm)], ['25', '26'])).
% 13.66/13.89  thf('28', plain,
% 13.66/13.89      (![X0 : $i]:
% 13.66/13.89         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 13.66/13.89      inference('demod', [status(thm)], ['9', '10'])).
% 13.66/13.89  thf('29', plain,
% 13.66/13.89      (![X0 : $i]:
% 13.66/13.89         (m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 13.66/13.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 13.66/13.89      inference('demod', [status(thm)], ['27', '28'])).
% 13.66/13.89  thf(cc1_relset_1, axiom,
% 13.66/13.89    (![A:$i,B:$i,C:$i]:
% 13.66/13.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.66/13.89       ( v1_relat_1 @ C ) ))).
% 13.66/13.89  thf('30', plain,
% 13.66/13.89      (![X30 : $i, X31 : $i, X32 : $i]:
% 13.66/13.89         ((v1_relat_1 @ X30)
% 13.66/13.89          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 13.66/13.89      inference('cnf', [status(esa)], [cc1_relset_1])).
% 13.66/13.89  thf('31', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['29', '30'])).
% 13.66/13.89  thf('32', plain,
% 13.66/13.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.66/13.89  thf('33', plain,
% 13.66/13.89      (![X30 : $i, X31 : $i, X32 : $i]:
% 13.66/13.89         ((v1_relat_1 @ X30)
% 13.66/13.89          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 13.66/13.89      inference('cnf', [status(esa)], [cc1_relset_1])).
% 13.66/13.89  thf('34', plain, ((v1_relat_1 @ sk_E)),
% 13.66/13.89      inference('sup-', [status(thm)], ['32', '33'])).
% 13.66/13.89  thf('35', plain, ((v5_relat_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C_1)),
% 13.66/13.89      inference('demod', [status(thm)], ['22', '31', '34'])).
% 13.66/13.89  thf('36', plain,
% 13.66/13.89      (![X18 : $i, X19 : $i]:
% 13.66/13.89         (~ (v5_relat_1 @ X18 @ X19)
% 13.66/13.89          | (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 13.66/13.89          | ~ (v1_relat_1 @ X18))),
% 13.66/13.89      inference('cnf', [status(esa)], [d19_relat_1])).
% 13.66/13.89  thf('37', plain,
% 13.66/13.89      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 13.66/13.89        | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C_1))),
% 13.66/13.89      inference('sup-', [status(thm)], ['35', '36'])).
% 13.66/13.89  thf('38', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['29', '30'])).
% 13.66/13.89  thf('39', plain,
% 13.66/13.89      ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C_1)),
% 13.66/13.89      inference('demod', [status(thm)], ['37', '38'])).
% 13.66/13.89  thf(d10_xboole_0, axiom,
% 13.66/13.89    (![A:$i,B:$i]:
% 13.66/13.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 13.66/13.89  thf('40', plain,
% 13.66/13.89      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 13.66/13.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 13.66/13.89  thf('41', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 13.66/13.89      inference('simplify', [status(thm)], ['40'])).
% 13.66/13.89  thf(t11_relset_1, axiom,
% 13.66/13.89    (![A:$i,B:$i,C:$i]:
% 13.66/13.89     ( ( v1_relat_1 @ C ) =>
% 13.66/13.89       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 13.66/13.89           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 13.66/13.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 13.66/13.89  thf('42', plain,
% 13.66/13.89      (![X43 : $i, X44 : $i, X45 : $i]:
% 13.66/13.89         (~ (r1_tarski @ (k1_relat_1 @ X43) @ X44)
% 13.66/13.89          | ~ (r1_tarski @ (k2_relat_1 @ X43) @ X45)
% 13.66/13.89          | (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 13.66/13.89          | ~ (v1_relat_1 @ X43))),
% 13.66/13.89      inference('cnf', [status(esa)], [t11_relset_1])).
% 13.66/13.89  thf('43', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i]:
% 13.66/13.89         (~ (v1_relat_1 @ X0)
% 13.66/13.89          | (m1_subset_1 @ X0 @ 
% 13.66/13.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 13.66/13.89          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 13.66/13.89      inference('sup-', [status(thm)], ['41', '42'])).
% 13.66/13.89  thf('44', plain,
% 13.66/13.89      (((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 13.66/13.89         (k1_zfmisc_1 @ 
% 13.66/13.89          (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C_1)))
% 13.66/13.89        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 13.66/13.89      inference('sup-', [status(thm)], ['39', '43'])).
% 13.66/13.89  thf('45', plain, ((r1_tarski @ sk_B @ sk_A)),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.66/13.89  thf('46', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_D)),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.66/13.89  thf(d1_funct_2, axiom,
% 13.66/13.89    (![A:$i,B:$i,C:$i]:
% 13.66/13.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.66/13.89       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 13.66/13.89           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 13.66/13.89             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 13.66/13.89         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 13.66/13.89           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 13.66/13.89             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 13.66/13.89  thf(zf_stmt_1, axiom,
% 13.66/13.89    (![C:$i,B:$i,A:$i]:
% 13.66/13.89     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 13.66/13.89       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 13.66/13.89  thf('47', plain,
% 13.66/13.89      (![X48 : $i, X49 : $i, X50 : $i]:
% 13.66/13.89         (~ (v1_funct_2 @ X50 @ X48 @ X49)
% 13.66/13.89          | ((X48) = (k1_relset_1 @ X48 @ X49 @ X50))
% 13.66/13.89          | ~ (zip_tseitin_1 @ X50 @ X49 @ X48))),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_1])).
% 13.66/13.89  thf('48', plain,
% 13.66/13.89      ((~ (zip_tseitin_1 @ sk_E @ sk_D @ sk_A)
% 13.66/13.89        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_D @ sk_E)))),
% 13.66/13.89      inference('sup-', [status(thm)], ['46', '47'])).
% 13.66/13.89  thf('49', plain,
% 13.66/13.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.66/13.89  thf(redefinition_k1_relset_1, axiom,
% 13.66/13.89    (![A:$i,B:$i,C:$i]:
% 13.66/13.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.66/13.89       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 13.66/13.89  thf('50', plain,
% 13.66/13.89      (![X36 : $i, X37 : $i, X38 : $i]:
% 13.66/13.89         (((k1_relset_1 @ X37 @ X38 @ X36) = (k1_relat_1 @ X36))
% 13.66/13.89          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 13.66/13.89      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 13.66/13.89  thf('51', plain,
% 13.66/13.89      (((k1_relset_1 @ sk_A @ sk_D @ sk_E) = (k1_relat_1 @ sk_E))),
% 13.66/13.89      inference('sup-', [status(thm)], ['49', '50'])).
% 13.66/13.89  thf('52', plain,
% 13.66/13.89      ((~ (zip_tseitin_1 @ sk_E @ sk_D @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_E)))),
% 13.66/13.89      inference('demod', [status(thm)], ['48', '51'])).
% 13.66/13.89  thf('53', plain,
% 13.66/13.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.66/13.89  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 13.66/13.89  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 13.66/13.89  thf(zf_stmt_4, axiom,
% 13.66/13.89    (![B:$i,A:$i]:
% 13.66/13.89     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 13.66/13.89       ( zip_tseitin_0 @ B @ A ) ))).
% 13.66/13.89  thf(zf_stmt_5, axiom,
% 13.66/13.89    (![A:$i,B:$i,C:$i]:
% 13.66/13.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.66/13.89       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 13.66/13.89         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 13.66/13.89           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 13.66/13.89             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 13.66/13.89  thf('54', plain,
% 13.66/13.89      (![X51 : $i, X52 : $i, X53 : $i]:
% 13.66/13.89         (~ (zip_tseitin_0 @ X51 @ X52)
% 13.66/13.89          | (zip_tseitin_1 @ X53 @ X51 @ X52)
% 13.66/13.89          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51))))),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 13.66/13.89  thf('55', plain,
% 13.66/13.89      (((zip_tseitin_1 @ sk_E @ sk_D @ sk_A) | ~ (zip_tseitin_0 @ sk_D @ sk_A))),
% 13.66/13.89      inference('sup-', [status(thm)], ['53', '54'])).
% 13.66/13.89  thf('56', plain,
% 13.66/13.89      (![X46 : $i, X47 : $i]:
% 13.66/13.89         ((zip_tseitin_0 @ X46 @ X47) | ((X46) = (k1_xboole_0)))),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_4])).
% 13.66/13.89  thf(t113_zfmisc_1, axiom,
% 13.66/13.89    (![A:$i,B:$i]:
% 13.66/13.89     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 13.66/13.89       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 13.66/13.89  thf('57', plain,
% 13.66/13.89      (![X8 : $i, X9 : $i]:
% 13.66/13.89         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 13.66/13.89      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 13.66/13.89  thf('58', plain,
% 13.66/13.89      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 13.66/13.89      inference('simplify', [status(thm)], ['57'])).
% 13.66/13.89  thf('59', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.66/13.89         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 13.66/13.89      inference('sup+', [status(thm)], ['56', '58'])).
% 13.66/13.89  thf(d3_tarski, axiom,
% 13.66/13.89    (![A:$i,B:$i]:
% 13.66/13.89     ( ( r1_tarski @ A @ B ) <=>
% 13.66/13.89       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 13.66/13.89  thf('60', plain,
% 13.66/13.89      (![X1 : $i, X3 : $i]:
% 13.66/13.89         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 13.66/13.89      inference('cnf', [status(esa)], [d3_tarski])).
% 13.66/13.89  thf('61', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 13.66/13.89      inference('simplify', [status(thm)], ['40'])).
% 13.66/13.89  thf(t3_subset, axiom,
% 13.66/13.89    (![A:$i,B:$i]:
% 13.66/13.89     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 13.66/13.89  thf('62', plain,
% 13.66/13.89      (![X10 : $i, X12 : $i]:
% 13.66/13.89         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 13.66/13.89      inference('cnf', [status(esa)], [t3_subset])).
% 13.66/13.89  thf('63', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['61', '62'])).
% 13.66/13.89  thf(t5_subset, axiom,
% 13.66/13.89    (![A:$i,B:$i,C:$i]:
% 13.66/13.89     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 13.66/13.89          ( v1_xboole_0 @ C ) ) ))).
% 13.66/13.89  thf('64', plain,
% 13.66/13.89      (![X13 : $i, X14 : $i, X15 : $i]:
% 13.66/13.89         (~ (r2_hidden @ X13 @ X14)
% 13.66/13.89          | ~ (v1_xboole_0 @ X15)
% 13.66/13.89          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 13.66/13.89      inference('cnf', [status(esa)], [t5_subset])).
% 13.66/13.89  thf('65', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['63', '64'])).
% 13.66/13.89  thf('66', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['60', '65'])).
% 13.66/13.89  thf('67', plain,
% 13.66/13.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.66/13.89  thf('68', plain,
% 13.66/13.89      (![X10 : $i, X11 : $i]:
% 13.66/13.89         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 13.66/13.89      inference('cnf', [status(esa)], [t3_subset])).
% 13.66/13.89  thf('69', plain, ((r1_tarski @ sk_E @ (k2_zfmisc_1 @ sk_A @ sk_D))),
% 13.66/13.89      inference('sup-', [status(thm)], ['67', '68'])).
% 13.66/13.89  thf('70', plain,
% 13.66/13.89      (![X4 : $i, X6 : $i]:
% 13.66/13.89         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 13.66/13.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 13.66/13.89  thf('71', plain,
% 13.66/13.89      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_D) @ sk_E)
% 13.66/13.89        | ((k2_zfmisc_1 @ sk_A @ sk_D) = (sk_E)))),
% 13.66/13.89      inference('sup-', [status(thm)], ['69', '70'])).
% 13.66/13.89  thf('72', plain,
% 13.66/13.89      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_D))
% 13.66/13.89        | ((k2_zfmisc_1 @ sk_A @ sk_D) = (sk_E)))),
% 13.66/13.89      inference('sup-', [status(thm)], ['66', '71'])).
% 13.66/13.89  thf('73', plain,
% 13.66/13.89      (![X0 : $i]:
% 13.66/13.89         (~ (v1_xboole_0 @ k1_xboole_0)
% 13.66/13.89          | (zip_tseitin_0 @ sk_D @ X0)
% 13.66/13.89          | ((k2_zfmisc_1 @ sk_A @ sk_D) = (sk_E)))),
% 13.66/13.89      inference('sup-', [status(thm)], ['59', '72'])).
% 13.66/13.89  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 13.66/13.89  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.66/13.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 13.66/13.89  thf('75', plain,
% 13.66/13.89      (![X0 : $i]:
% 13.66/13.89         ((zip_tseitin_0 @ sk_D @ X0) | ((k2_zfmisc_1 @ sk_A @ sk_D) = (sk_E)))),
% 13.66/13.89      inference('demod', [status(thm)], ['73', '74'])).
% 13.66/13.89  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.66/13.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 13.66/13.89  thf('77', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['60', '65'])).
% 13.66/13.89  thf('78', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['60', '65'])).
% 13.66/13.89  thf('79', plain,
% 13.66/13.89      (![X4 : $i, X6 : $i]:
% 13.66/13.89         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 13.66/13.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 13.66/13.89  thf('80', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i]:
% 13.66/13.89         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 13.66/13.89      inference('sup-', [status(thm)], ['78', '79'])).
% 13.66/13.89  thf('81', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i]:
% 13.66/13.89         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['77', '80'])).
% 13.66/13.89  thf('82', plain,
% 13.66/13.89      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 13.66/13.89      inference('sup-', [status(thm)], ['76', '81'])).
% 13.66/13.89  thf('83', plain,
% 13.66/13.89      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 13.66/13.89      inference('simplify', [status(thm)], ['57'])).
% 13.66/13.89  thf('84', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i]:
% 13.66/13.89         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 13.66/13.89      inference('sup+', [status(thm)], ['82', '83'])).
% 13.66/13.89  thf('85', plain,
% 13.66/13.89      (![X0 : $i]:
% 13.66/13.89         (((sk_E) = (k1_xboole_0))
% 13.66/13.89          | (zip_tseitin_0 @ sk_D @ X0)
% 13.66/13.89          | ~ (v1_xboole_0 @ sk_D))),
% 13.66/13.89      inference('sup+', [status(thm)], ['75', '84'])).
% 13.66/13.89  thf('86', plain, (~ (v1_xboole_0 @ sk_D)),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.66/13.89  thf('87', plain,
% 13.66/13.89      (![X0 : $i]: (~ (v1_xboole_0 @ sk_D) | (zip_tseitin_0 @ sk_D @ X0))),
% 13.66/13.89      inference('clc', [status(thm)], ['85', '86'])).
% 13.66/13.89  thf('88', plain,
% 13.66/13.89      (![X46 : $i, X47 : $i]:
% 13.66/13.89         ((zip_tseitin_0 @ X46 @ X47) | ((X46) = (k1_xboole_0)))),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_4])).
% 13.66/13.89  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.66/13.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 13.66/13.89  thf('90', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 13.66/13.89      inference('sup+', [status(thm)], ['88', '89'])).
% 13.66/13.89  thf('91', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_D @ X0)),
% 13.66/13.89      inference('clc', [status(thm)], ['87', '90'])).
% 13.66/13.89  thf('92', plain, ((zip_tseitin_1 @ sk_E @ sk_D @ sk_A)),
% 13.66/13.89      inference('demod', [status(thm)], ['55', '91'])).
% 13.66/13.89  thf('93', plain, (((sk_A) = (k1_relat_1 @ sk_E))),
% 13.66/13.89      inference('demod', [status(thm)], ['52', '92'])).
% 13.66/13.89  thf(t91_relat_1, axiom,
% 13.66/13.89    (![A:$i,B:$i]:
% 13.66/13.89     ( ( v1_relat_1 @ B ) =>
% 13.66/13.89       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 13.66/13.89         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 13.66/13.89  thf('94', plain,
% 13.66/13.89      (![X28 : $i, X29 : $i]:
% 13.66/13.89         (~ (r1_tarski @ X28 @ (k1_relat_1 @ X29))
% 13.66/13.89          | ((k1_relat_1 @ (k7_relat_1 @ X29 @ X28)) = (X28))
% 13.66/13.89          | ~ (v1_relat_1 @ X29))),
% 13.66/13.89      inference('cnf', [status(esa)], [t91_relat_1])).
% 13.66/13.89  thf('95', plain,
% 13.66/13.89      (![X0 : $i]:
% 13.66/13.89         (~ (r1_tarski @ X0 @ sk_A)
% 13.66/13.89          | ~ (v1_relat_1 @ sk_E)
% 13.66/13.89          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 13.66/13.89      inference('sup-', [status(thm)], ['93', '94'])).
% 13.66/13.89  thf('96', plain, ((v1_relat_1 @ sk_E)),
% 13.66/13.89      inference('sup-', [status(thm)], ['32', '33'])).
% 13.66/13.89  thf('97', plain,
% 13.66/13.89      (![X0 : $i]:
% 13.66/13.89         (~ (r1_tarski @ X0 @ sk_A)
% 13.66/13.89          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 13.66/13.89      inference('demod', [status(thm)], ['95', '96'])).
% 13.66/13.89  thf('98', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 13.66/13.89      inference('sup-', [status(thm)], ['45', '97'])).
% 13.66/13.89  thf('99', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['29', '30'])).
% 13.66/13.89  thf('100', plain,
% 13.66/13.89      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 13.66/13.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 13.66/13.89      inference('demod', [status(thm)], ['44', '98', '99'])).
% 13.66/13.89  thf('101', plain,
% 13.66/13.89      (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C_1)),
% 13.66/13.89      inference('demod', [status(thm)], ['13', '100'])).
% 13.66/13.89  thf('102', plain,
% 13.66/13.89      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 13.66/13.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 13.66/13.89      inference('demod', [status(thm)], ['44', '98', '99'])).
% 13.66/13.89  thf('103', plain,
% 13.66/13.89      (![X36 : $i, X37 : $i, X38 : $i]:
% 13.66/13.89         (((k1_relset_1 @ X37 @ X38 @ X36) = (k1_relat_1 @ X36))
% 13.66/13.89          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 13.66/13.89      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 13.66/13.89  thf('104', plain,
% 13.66/13.89      (((k1_relset_1 @ sk_B @ sk_C_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 13.66/13.89         = (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 13.66/13.89      inference('sup-', [status(thm)], ['102', '103'])).
% 13.66/13.89  thf('105', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 13.66/13.89      inference('sup-', [status(thm)], ['45', '97'])).
% 13.66/13.89  thf('106', plain,
% 13.66/13.89      (((k1_relset_1 @ sk_B @ sk_C_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 13.66/13.89      inference('demod', [status(thm)], ['104', '105'])).
% 13.66/13.89  thf('107', plain,
% 13.66/13.89      (![X48 : $i, X49 : $i, X50 : $i]:
% 13.66/13.89         (((X48) != (k1_relset_1 @ X48 @ X49 @ X50))
% 13.66/13.89          | (v1_funct_2 @ X50 @ X48 @ X49)
% 13.66/13.89          | ~ (zip_tseitin_1 @ X50 @ X49 @ X48))),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_1])).
% 13.66/13.89  thf('108', plain,
% 13.66/13.89      ((((sk_B) != (sk_B))
% 13.66/13.89        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C_1 @ sk_B)
% 13.66/13.89        | (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C_1))),
% 13.66/13.89      inference('sup-', [status(thm)], ['106', '107'])).
% 13.66/13.89  thf('109', plain,
% 13.66/13.89      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C_1)
% 13.66/13.89        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C_1 @ sk_B))),
% 13.66/13.89      inference('simplify', [status(thm)], ['108'])).
% 13.66/13.89  thf('110', plain,
% 13.66/13.89      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 13.66/13.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 13.66/13.89      inference('demod', [status(thm)], ['44', '98', '99'])).
% 13.66/13.89  thf('111', plain,
% 13.66/13.89      (![X51 : $i, X52 : $i, X53 : $i]:
% 13.66/13.89         (~ (zip_tseitin_0 @ X51 @ X52)
% 13.66/13.89          | (zip_tseitin_1 @ X53 @ X51 @ X52)
% 13.66/13.89          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51))))),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 13.66/13.89  thf('112', plain,
% 13.66/13.89      (((zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C_1 @ sk_B)
% 13.66/13.89        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_B))),
% 13.66/13.89      inference('sup-', [status(thm)], ['110', '111'])).
% 13.66/13.89  thf('113', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.66/13.89         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 13.66/13.89      inference('sup+', [status(thm)], ['56', '58'])).
% 13.66/13.89  thf('114', plain,
% 13.66/13.89      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 13.66/13.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 13.66/13.89      inference('demod', [status(thm)], ['44', '98', '99'])).
% 13.66/13.89  thf('115', plain,
% 13.66/13.89      (![X10 : $i, X11 : $i]:
% 13.66/13.89         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 13.66/13.89      inference('cnf', [status(esa)], [t3_subset])).
% 13.66/13.89  thf('116', plain,
% 13.66/13.89      ((r1_tarski @ (k7_relat_1 @ sk_E @ sk_B) @ (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 13.66/13.89      inference('sup-', [status(thm)], ['114', '115'])).
% 13.66/13.89  thf('117', plain,
% 13.66/13.89      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 13.66/13.89      inference('sup-', [status(thm)], ['76', '81'])).
% 13.66/13.89  thf('118', plain,
% 13.66/13.89      (![X8 : $i, X9 : $i]:
% 13.66/13.89         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 13.66/13.89      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 13.66/13.89  thf('119', plain,
% 13.66/13.89      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 13.66/13.89      inference('simplify', [status(thm)], ['118'])).
% 13.66/13.89  thf('120', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['61', '62'])).
% 13.66/13.89  thf(cc2_relset_1, axiom,
% 13.66/13.89    (![A:$i,B:$i,C:$i]:
% 13.66/13.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.66/13.89       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 13.66/13.89  thf('121', plain,
% 13.66/13.89      (![X33 : $i, X34 : $i, X35 : $i]:
% 13.66/13.89         ((v5_relat_1 @ X33 @ X35)
% 13.66/13.89          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 13.66/13.89      inference('cnf', [status(esa)], [cc2_relset_1])).
% 13.66/13.89  thf('122', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i]: (v5_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X0)),
% 13.66/13.89      inference('sup-', [status(thm)], ['120', '121'])).
% 13.66/13.89  thf('123', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 13.66/13.89      inference('sup+', [status(thm)], ['119', '122'])).
% 13.66/13.89  thf('124', plain,
% 13.66/13.89      (![X18 : $i, X19 : $i]:
% 13.66/13.89         (~ (v5_relat_1 @ X18 @ X19)
% 13.66/13.89          | (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 13.66/13.89          | ~ (v1_relat_1 @ X18))),
% 13.66/13.89      inference('cnf', [status(esa)], [d19_relat_1])).
% 13.66/13.89  thf('125', plain,
% 13.66/13.89      (![X0 : $i]:
% 13.66/13.89         (~ (v1_relat_1 @ k1_xboole_0)
% 13.66/13.89          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['123', '124'])).
% 13.66/13.89  thf('126', plain,
% 13.66/13.89      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 13.66/13.89      inference('simplify', [status(thm)], ['118'])).
% 13.66/13.89  thf(fc6_relat_1, axiom,
% 13.66/13.89    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 13.66/13.89  thf('127', plain,
% 13.66/13.89      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 13.66/13.89      inference('cnf', [status(esa)], [fc6_relat_1])).
% 13.66/13.89  thf('128', plain, ((v1_relat_1 @ k1_xboole_0)),
% 13.66/13.89      inference('sup+', [status(thm)], ['126', '127'])).
% 13.66/13.89  thf('129', plain,
% 13.66/13.89      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 13.66/13.89      inference('demod', [status(thm)], ['125', '128'])).
% 13.66/13.89  thf('130', plain,
% 13.66/13.89      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 13.66/13.89      inference('simplify', [status(thm)], ['57'])).
% 13.66/13.89  thf('131', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i]: (v5_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X0)),
% 13.66/13.89      inference('sup-', [status(thm)], ['120', '121'])).
% 13.66/13.89  thf('132', plain, ((v5_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 13.66/13.89      inference('sup+', [status(thm)], ['130', '131'])).
% 13.66/13.89  thf('133', plain,
% 13.66/13.89      (![X18 : $i, X19 : $i]:
% 13.66/13.89         (~ (v5_relat_1 @ X18 @ X19)
% 13.66/13.89          | (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 13.66/13.89          | ~ (v1_relat_1 @ X18))),
% 13.66/13.89      inference('cnf', [status(esa)], [d19_relat_1])).
% 13.66/13.89  thf('134', plain,
% 13.66/13.89      ((~ (v1_relat_1 @ k1_xboole_0)
% 13.66/13.89        | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['132', '133'])).
% 13.66/13.89  thf('135', plain, ((v1_relat_1 @ k1_xboole_0)),
% 13.66/13.89      inference('sup+', [status(thm)], ['126', '127'])).
% 13.66/13.89  thf('136', plain, ((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 13.66/13.89      inference('demod', [status(thm)], ['134', '135'])).
% 13.66/13.89  thf('137', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i]:
% 13.66/13.89         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 13.66/13.89      inference('sup-', [status(thm)], ['78', '79'])).
% 13.66/13.89  thf('138', plain,
% 13.66/13.89      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 13.66/13.89        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['136', '137'])).
% 13.66/13.89  thf('139', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.66/13.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 13.66/13.89  thf('140', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 13.66/13.89      inference('demod', [status(thm)], ['138', '139'])).
% 13.66/13.89  thf('141', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 13.66/13.89      inference('demod', [status(thm)], ['129', '140'])).
% 13.66/13.89  thf('142', plain,
% 13.66/13.89      (![X4 : $i, X6 : $i]:
% 13.66/13.89         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 13.66/13.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 13.66/13.89  thf('143', plain,
% 13.66/13.89      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 13.66/13.89      inference('sup-', [status(thm)], ['141', '142'])).
% 13.66/13.89  thf('144', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i]:
% 13.66/13.89         (~ (r1_tarski @ X1 @ X0)
% 13.66/13.89          | ~ (v1_xboole_0 @ X0)
% 13.66/13.89          | ((X1) = (k1_xboole_0)))),
% 13.66/13.89      inference('sup-', [status(thm)], ['117', '143'])).
% 13.66/13.89  thf('145', plain,
% 13.66/13.89      ((((k7_relat_1 @ sk_E @ sk_B) = (k1_xboole_0))
% 13.66/13.89        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 13.66/13.89      inference('sup-', [status(thm)], ['116', '144'])).
% 13.66/13.89  thf('146', plain,
% 13.66/13.89      (![X0 : $i]:
% 13.66/13.89         (~ (v1_xboole_0 @ k1_xboole_0)
% 13.66/13.89          | (zip_tseitin_0 @ sk_C_1 @ X0)
% 13.66/13.89          | ((k7_relat_1 @ sk_E @ sk_B) = (k1_xboole_0)))),
% 13.66/13.89      inference('sup-', [status(thm)], ['113', '145'])).
% 13.66/13.89  thf('147', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.66/13.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 13.66/13.89  thf('148', plain,
% 13.66/13.89      (![X0 : $i]:
% 13.66/13.89         ((zip_tseitin_0 @ sk_C_1 @ X0)
% 13.66/13.89          | ((k7_relat_1 @ sk_E @ sk_B) = (k1_xboole_0)))),
% 13.66/13.89      inference('demod', [status(thm)], ['146', '147'])).
% 13.66/13.89  thf('149', plain,
% 13.66/13.89      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 13.66/13.89      inference('sup-', [status(thm)], ['76', '81'])).
% 13.66/13.89  thf('150', plain,
% 13.66/13.89      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 13.66/13.89      inference('sup-', [status(thm)], ['76', '81'])).
% 13.66/13.89  thf('151', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 13.66/13.89      inference('demod', [status(thm)], ['129', '140'])).
% 13.66/13.89  thf('152', plain,
% 13.66/13.89      (![X10 : $i, X12 : $i]:
% 13.66/13.89         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 13.66/13.89      inference('cnf', [status(esa)], [t3_subset])).
% 13.66/13.89  thf('153', plain,
% 13.66/13.89      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['151', '152'])).
% 13.66/13.89  thf('154', plain,
% 13.66/13.89      (![X36 : $i, X37 : $i, X38 : $i]:
% 13.66/13.89         (((k1_relset_1 @ X37 @ X38 @ X36) = (k1_relat_1 @ X36))
% 13.66/13.89          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 13.66/13.89      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 13.66/13.89  thf('155', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i]:
% 13.66/13.89         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['153', '154'])).
% 13.66/13.89  thf('156', plain,
% 13.66/13.89      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 13.66/13.89      inference('simplify', [status(thm)], ['57'])).
% 13.66/13.89  thf('157', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['61', '62'])).
% 13.66/13.89  thf('158', plain,
% 13.66/13.89      (![X33 : $i, X34 : $i, X35 : $i]:
% 13.66/13.89         ((v4_relat_1 @ X33 @ X34)
% 13.66/13.89          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 13.66/13.89      inference('cnf', [status(esa)], [cc2_relset_1])).
% 13.66/13.89  thf('159', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 13.66/13.89      inference('sup-', [status(thm)], ['157', '158'])).
% 13.66/13.89  thf('160', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 13.66/13.89      inference('sup+', [status(thm)], ['156', '159'])).
% 13.66/13.89  thf(d18_relat_1, axiom,
% 13.66/13.89    (![A:$i,B:$i]:
% 13.66/13.89     ( ( v1_relat_1 @ B ) =>
% 13.66/13.89       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 13.66/13.89  thf('161', plain,
% 13.66/13.89      (![X16 : $i, X17 : $i]:
% 13.66/13.89         (~ (v4_relat_1 @ X16 @ X17)
% 13.66/13.89          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 13.66/13.89          | ~ (v1_relat_1 @ X16))),
% 13.66/13.89      inference('cnf', [status(esa)], [d18_relat_1])).
% 13.66/13.89  thf('162', plain,
% 13.66/13.89      (![X0 : $i]:
% 13.66/13.89         (~ (v1_relat_1 @ k1_xboole_0)
% 13.66/13.89          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['160', '161'])).
% 13.66/13.89  thf('163', plain, ((v1_relat_1 @ k1_xboole_0)),
% 13.66/13.89      inference('sup+', [status(thm)], ['126', '127'])).
% 13.66/13.89  thf('164', plain,
% 13.66/13.89      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 13.66/13.89      inference('demod', [status(thm)], ['162', '163'])).
% 13.66/13.89  thf('165', plain,
% 13.66/13.89      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 13.66/13.89      inference('sup-', [status(thm)], ['141', '142'])).
% 13.66/13.89  thf('166', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['164', '165'])).
% 13.66/13.89  thf('167', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i]:
% 13.66/13.89         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 13.66/13.89      inference('demod', [status(thm)], ['155', '166'])).
% 13.66/13.89  thf('168', plain,
% 13.66/13.89      (![X48 : $i, X49 : $i, X50 : $i]:
% 13.66/13.89         (((X48) != (k1_relset_1 @ X48 @ X49 @ X50))
% 13.66/13.89          | (v1_funct_2 @ X50 @ X48 @ X49)
% 13.66/13.89          | ~ (zip_tseitin_1 @ X50 @ X49 @ X48))),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_1])).
% 13.66/13.89  thf('169', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i]:
% 13.66/13.89         (((X1) != (k1_xboole_0))
% 13.66/13.89          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 13.66/13.89          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['167', '168'])).
% 13.66/13.89  thf('170', plain,
% 13.66/13.89      (![X0 : $i]:
% 13.66/13.89         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 13.66/13.89          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 13.66/13.89      inference('simplify', [status(thm)], ['169'])).
% 13.66/13.89  thf('171', plain,
% 13.66/13.89      (![X46 : $i, X47 : $i]:
% 13.66/13.89         ((zip_tseitin_0 @ X46 @ X47) | ((X47) != (k1_xboole_0)))),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_4])).
% 13.66/13.89  thf('172', plain, (![X46 : $i]: (zip_tseitin_0 @ X46 @ k1_xboole_0)),
% 13.66/13.89      inference('simplify', [status(thm)], ['171'])).
% 13.66/13.89  thf('173', plain,
% 13.66/13.89      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['151', '152'])).
% 13.66/13.89  thf('174', plain,
% 13.66/13.89      (![X51 : $i, X52 : $i, X53 : $i]:
% 13.66/13.89         (~ (zip_tseitin_0 @ X51 @ X52)
% 13.66/13.89          | (zip_tseitin_1 @ X53 @ X51 @ X52)
% 13.66/13.89          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51))))),
% 13.66/13.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 13.66/13.89  thf('175', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i]:
% 13.66/13.89         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 13.66/13.89      inference('sup-', [status(thm)], ['173', '174'])).
% 13.66/13.89  thf('176', plain,
% 13.66/13.89      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 13.66/13.89      inference('sup-', [status(thm)], ['172', '175'])).
% 13.66/13.89  thf('177', plain,
% 13.66/13.89      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 13.66/13.89      inference('demod', [status(thm)], ['170', '176'])).
% 13.66/13.89  thf('178', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i]:
% 13.66/13.89         ((v1_funct_2 @ X0 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 13.66/13.89      inference('sup+', [status(thm)], ['150', '177'])).
% 13.66/13.89  thf('179', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.66/13.89         ((v1_funct_2 @ X2 @ X0 @ X1)
% 13.66/13.89          | ~ (v1_xboole_0 @ X0)
% 13.66/13.89          | ~ (v1_xboole_0 @ X2))),
% 13.66/13.89      inference('sup+', [status(thm)], ['149', '178'])).
% 13.66/13.89  thf('180', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['60', '65'])).
% 13.66/13.89  thf('181', plain,
% 13.66/13.89      (![X10 : $i, X12 : $i]:
% 13.66/13.89         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 13.66/13.89      inference('cnf', [status(esa)], [t3_subset])).
% 13.66/13.89  thf('182', plain,
% 13.66/13.89      (![X0 : $i, X1 : $i]:
% 13.66/13.89         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 13.66/13.89      inference('sup-', [status(thm)], ['180', '181'])).
% 13.66/13.89  thf('183', plain,
% 13.66/13.89      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C_1)
% 13.66/13.89        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 13.66/13.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1))))),
% 13.66/13.89      inference('demod', [status(thm)], ['6', '11', '12'])).
% 13.66/13.89  thf('184', plain,
% 13.66/13.89      ((~ (v1_xboole_0 @ (k7_relat_1 @ sk_E @ sk_B))
% 13.66/13.89        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C_1))),
% 13.66/13.89      inference('sup-', [status(thm)], ['182', '183'])).
% 13.66/13.89  thf('185', plain,
% 13.66/13.89      ((~ (v1_xboole_0 @ (k7_relat_1 @ sk_E @ sk_B))
% 13.66/13.89        | ~ (v1_xboole_0 @ sk_B)
% 13.66/13.89        | ~ (v1_xboole_0 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 13.66/13.89      inference('sup-', [status(thm)], ['179', '184'])).
% 13.66/13.89  thf('186', plain,
% 13.66/13.89      ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 13.66/13.89      inference('simplify', [status(thm)], ['185'])).
% 13.66/13.89  thf('187', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 13.66/13.89      inference('sup-', [status(thm)], ['45', '97'])).
% 13.66/13.89  thf('188', plain,
% 13.66/13.89      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 13.66/13.89      inference('sup-', [status(thm)], ['76', '81'])).
% 13.66/13.89  thf('189', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['164', '165'])).
% 13.66/13.89  thf('190', plain,
% 13.66/13.89      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 13.66/13.89      inference('sup+', [status(thm)], ['188', '189'])).
% 13.66/13.89  thf('191', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.66/13.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 13.66/13.89  thf('192', plain,
% 13.66/13.89      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 13.66/13.89      inference('sup+', [status(thm)], ['190', '191'])).
% 13.66/13.89  thf('193', plain,
% 13.66/13.89      (((v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 13.66/13.89      inference('sup+', [status(thm)], ['187', '192'])).
% 13.66/13.89  thf('194', plain, (~ (v1_xboole_0 @ (k7_relat_1 @ sk_E @ sk_B))),
% 13.66/13.89      inference('clc', [status(thm)], ['186', '193'])).
% 13.66/13.89  thf('195', plain,
% 13.66/13.89      (![X0 : $i]:
% 13.66/13.89         (~ (v1_xboole_0 @ k1_xboole_0) | (zip_tseitin_0 @ sk_C_1 @ X0))),
% 13.66/13.89      inference('sup-', [status(thm)], ['148', '194'])).
% 13.66/13.89  thf('196', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.66/13.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 13.66/13.89  thf('197', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C_1 @ X0)),
% 13.66/13.89      inference('demod', [status(thm)], ['195', '196'])).
% 13.66/13.89  thf('198', plain,
% 13.66/13.89      ((zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C_1 @ sk_B)),
% 13.66/13.89      inference('demod', [status(thm)], ['112', '197'])).
% 13.66/13.89  thf('199', plain,
% 13.66/13.89      ((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C_1)),
% 13.66/13.89      inference('demod', [status(thm)], ['109', '198'])).
% 13.66/13.89  thf('200', plain, ($false), inference('demod', [status(thm)], ['101', '199'])).
% 13.66/13.89  
% 13.66/13.89  % SZS output end Refutation
% 13.66/13.89  
% 13.66/13.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

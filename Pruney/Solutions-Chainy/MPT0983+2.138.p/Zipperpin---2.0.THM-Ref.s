%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N1yA3H6Ep4

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:23 EST 2020

% Result     : Theorem 5.88s
% Output     : Refutation 5.88s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 554 expanded)
%              Number of leaves         :   46 ( 181 expanded)
%              Depth                    :   20
%              Number of atoms          : 1348 (9027 expanded)
%              Number of equality atoms :   65 ( 182 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('0',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('4',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ( ( k1_partfun1 @ X53 @ X54 @ X56 @ X57 @ X52 @ X55 )
        = ( k5_relat_1 @ X52 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
      = ( k5_relat_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('20',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( X38 = X41 )
      | ~ ( r2_relset_1 @ X39 @ X40 @ X38 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('23',plain,(
    ! [X51: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X51 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('24',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['8','9','24'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('26',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) ) @ ( k2_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('30',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('31',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('32',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X23 ) )
      = X23 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v5_relat_1 @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('35',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('41',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('42',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['8','9','24'])).

thf('45',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X23 ) )
      = X23 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('47',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('51',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['29','32','43','44','45','46','51'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('53',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k2_relat_1 @ X43 )
       != X42 )
      | ( v2_funct_2 @ X43 @ X42 )
      | ~ ( v5_relat_1 @ X43 @ X42 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('54',plain,(
    ! [X43: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ~ ( v5_relat_1 @ X43 @ ( k2_relat_1 @ X43 ) )
      | ( v2_funct_2 @ X43 @ ( k2_relat_1 @ X43 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ( v5_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X43: $i] :
      ( ( v2_funct_2 @ X43 @ ( k2_relat_1 @ X43 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(clc,[status(thm)],['54','58'])).

thf('60',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['52','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('62',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('69',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('71',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('72',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( r2_relset_1 @ X39 @ X40 @ X38 @ X41 )
      | ( X38 != X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('73',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( r2_relset_1 @ X39 @ X40 @ X41 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','74'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('76',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('77',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X51: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X51 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('79',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( X38 = X41 )
      | ~ ( r2_relset_1 @ X39 @ X40 @ X38 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k6_partfun1 @ k1_xboole_0 )
        = X0 )
      | ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('83',plain,(
    ! [X51: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X51 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('84',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('86',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('87',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X34 ) ) )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('88',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    v1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('93',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['91','92'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0 = X0 )
      | ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['75','95'])).

thf('97',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X1 ) ) ),
    inference('sup-',[status(thm)],['69','98'])).

thf('100',plain,
    ( ( k1_xboole_0 = sk_C_1 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['68','99'])).

thf('101',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('102',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('103',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_funct_2 @ X59 @ X60 @ X61 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X62 @ X60 @ X60 @ X61 @ X63 @ X59 ) )
      | ( v2_funct_1 @ X63 )
      | ( X61 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X60 ) ) )
      | ~ ( v1_funct_2 @ X63 @ X62 @ X60 )
      | ~ ( v1_funct_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['101','107'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('109',plain,(
    ! [X28: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('110',plain,(
    ! [X58: $i] :
      ( ( k6_partfun1 @ X58 )
      = ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('111',plain,(
    ! [X28: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X28 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['108','111','112','113','114'])).

thf('116',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','66'])).

thf('117',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('119',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('120',plain,(
    k1_xboole_0 = sk_C_1 ),
    inference(demod,[status(thm)],['100','117','118','119'])).

thf('121',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['91','92'])).

thf('122',plain,(
    ! [X28: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X28 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('123',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    $false ),
    inference(demod,[status(thm)],['67','120','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N1yA3H6Ep4
% 0.16/0.38  % Computer   : n023.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 16:21:06 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 5.88/6.12  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.88/6.12  % Solved by: fo/fo7.sh
% 5.88/6.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.88/6.12  % done 7246 iterations in 5.659s
% 5.88/6.12  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.88/6.12  % SZS output start Refutation
% 5.88/6.12  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.88/6.12  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 5.88/6.12  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 5.88/6.12  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.88/6.12  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.88/6.12  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.88/6.12  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.88/6.12  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 5.88/6.12  thf(sk_B_1_type, type, sk_B_1: $i).
% 5.88/6.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.88/6.12  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 5.88/6.12  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 5.88/6.12  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 5.88/6.12  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.88/6.12  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 5.88/6.12  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 5.88/6.12  thf(sk_A_type, type, sk_A: $i).
% 5.88/6.12  thf(sk_C_1_type, type, sk_C_1: $i).
% 5.88/6.12  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 5.88/6.12  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 5.88/6.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.88/6.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.88/6.12  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.88/6.12  thf(sk_D_type, type, sk_D: $i).
% 5.88/6.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.88/6.12  thf(t29_funct_2, conjecture,
% 5.88/6.12    (![A:$i,B:$i,C:$i]:
% 5.88/6.12     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.88/6.12         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.88/6.12       ( ![D:$i]:
% 5.88/6.12         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.88/6.12             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.88/6.12           ( ( r2_relset_1 @
% 5.88/6.12               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.88/6.12               ( k6_partfun1 @ A ) ) =>
% 5.88/6.12             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 5.88/6.12  thf(zf_stmt_0, negated_conjecture,
% 5.88/6.12    (~( ![A:$i,B:$i,C:$i]:
% 5.88/6.12        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.88/6.12            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.88/6.12          ( ![D:$i]:
% 5.88/6.12            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.88/6.12                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.88/6.12              ( ( r2_relset_1 @
% 5.88/6.12                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.88/6.12                  ( k6_partfun1 @ A ) ) =>
% 5.88/6.12                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 5.88/6.12    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 5.88/6.12  thf('0', plain, ((~ (v2_funct_1 @ sk_C_1) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 5.88/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.88/6.12  thf('1', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 5.88/6.12      inference('split', [status(esa)], ['0'])).
% 5.88/6.12  thf('2', plain,
% 5.88/6.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.88/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.88/6.12  thf('3', plain,
% 5.88/6.12      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.88/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.88/6.12  thf(redefinition_k1_partfun1, axiom,
% 5.88/6.12    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.88/6.12     ( ( ( v1_funct_1 @ E ) & 
% 5.88/6.12         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.88/6.12         ( v1_funct_1 @ F ) & 
% 5.88/6.12         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.88/6.12       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 5.88/6.12  thf('4', plain,
% 5.88/6.12      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 5.88/6.12         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 5.88/6.12          | ~ (v1_funct_1 @ X52)
% 5.88/6.12          | ~ (v1_funct_1 @ X55)
% 5.88/6.12          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 5.88/6.12          | ((k1_partfun1 @ X53 @ X54 @ X56 @ X57 @ X52 @ X55)
% 5.88/6.12              = (k5_relat_1 @ X52 @ X55)))),
% 5.88/6.12      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 5.88/6.12  thf('5', plain,
% 5.88/6.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.88/6.12         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0)
% 5.88/6.12            = (k5_relat_1 @ sk_C_1 @ X0))
% 5.88/6.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.88/6.12          | ~ (v1_funct_1 @ X0)
% 5.88/6.12          | ~ (v1_funct_1 @ sk_C_1))),
% 5.88/6.12      inference('sup-', [status(thm)], ['3', '4'])).
% 5.88/6.12  thf('6', plain, ((v1_funct_1 @ sk_C_1)),
% 5.88/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.88/6.12  thf('7', plain,
% 5.88/6.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.88/6.12         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0)
% 5.88/6.12            = (k5_relat_1 @ sk_C_1 @ X0))
% 5.88/6.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.88/6.12          | ~ (v1_funct_1 @ X0))),
% 5.88/6.12      inference('demod', [status(thm)], ['5', '6'])).
% 5.88/6.12  thf('8', plain,
% 5.88/6.12      ((~ (v1_funct_1 @ sk_D)
% 5.88/6.12        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 5.88/6.12            = (k5_relat_1 @ sk_C_1 @ sk_D)))),
% 5.88/6.12      inference('sup-', [status(thm)], ['2', '7'])).
% 5.88/6.12  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 5.88/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.88/6.12  thf('10', plain,
% 5.88/6.12      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.88/6.12        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 5.88/6.12        (k6_partfun1 @ sk_A))),
% 5.88/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.88/6.12  thf('11', plain,
% 5.88/6.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.88/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.88/6.12  thf('12', plain,
% 5.88/6.12      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.88/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.88/6.12  thf(dt_k1_partfun1, axiom,
% 5.88/6.12    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.88/6.12     ( ( ( v1_funct_1 @ E ) & 
% 5.88/6.12         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.88/6.12         ( v1_funct_1 @ F ) & 
% 5.88/6.12         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.88/6.12       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 5.88/6.12         ( m1_subset_1 @
% 5.88/6.12           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 5.88/6.12           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 5.88/6.12  thf('13', plain,
% 5.88/6.12      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 5.88/6.12         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 5.88/6.12          | ~ (v1_funct_1 @ X44)
% 5.88/6.12          | ~ (v1_funct_1 @ X47)
% 5.88/6.12          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 5.88/6.12          | (m1_subset_1 @ (k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47) @ 
% 5.88/6.12             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X49))))),
% 5.88/6.12      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 5.88/6.12  thf('14', plain,
% 5.88/6.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.88/6.12         ((m1_subset_1 @ 
% 5.88/6.12           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 5.88/6.12           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.88/6.12          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.88/6.12          | ~ (v1_funct_1 @ X1)
% 5.88/6.12          | ~ (v1_funct_1 @ sk_C_1))),
% 5.88/6.12      inference('sup-', [status(thm)], ['12', '13'])).
% 5.88/6.12  thf('15', plain, ((v1_funct_1 @ sk_C_1)),
% 5.88/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.88/6.12  thf('16', plain,
% 5.88/6.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.88/6.12         ((m1_subset_1 @ 
% 5.88/6.12           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 5.88/6.12           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.88/6.12          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.88/6.12          | ~ (v1_funct_1 @ X1))),
% 5.88/6.12      inference('demod', [status(thm)], ['14', '15'])).
% 5.88/6.12  thf('17', plain,
% 5.88/6.12      ((~ (v1_funct_1 @ sk_D)
% 5.88/6.12        | (m1_subset_1 @ 
% 5.88/6.12           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 5.88/6.12           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.88/6.12      inference('sup-', [status(thm)], ['11', '16'])).
% 5.88/6.12  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 5.88/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.88/6.12  thf('19', plain,
% 5.88/6.12      ((m1_subset_1 @ 
% 5.88/6.12        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 5.88/6.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.88/6.12      inference('demod', [status(thm)], ['17', '18'])).
% 5.88/6.12  thf(redefinition_r2_relset_1, axiom,
% 5.88/6.12    (![A:$i,B:$i,C:$i,D:$i]:
% 5.88/6.12     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.88/6.12         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.88/6.12       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 5.88/6.12  thf('20', plain,
% 5.88/6.12      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 5.88/6.12         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 5.88/6.12          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 5.88/6.12          | ((X38) = (X41))
% 5.88/6.12          | ~ (r2_relset_1 @ X39 @ X40 @ X38 @ X41))),
% 5.88/6.12      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.88/6.12  thf('21', plain,
% 5.88/6.12      (![X0 : $i]:
% 5.88/6.12         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.88/6.12             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ X0)
% 5.88/6.12          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 5.88/6.12              = (X0))
% 5.88/6.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.88/6.12      inference('sup-', [status(thm)], ['19', '20'])).
% 5.88/6.12  thf('22', plain,
% 5.88/6.12      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 5.88/6.12           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.88/6.12        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 5.88/6.12            = (k6_partfun1 @ sk_A)))),
% 5.88/6.12      inference('sup-', [status(thm)], ['10', '21'])).
% 5.88/6.12  thf(dt_k6_partfun1, axiom,
% 5.88/6.12    (![A:$i]:
% 5.88/6.12     ( ( m1_subset_1 @
% 5.88/6.12         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 5.88/6.12       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 5.88/6.12  thf('23', plain,
% 5.88/6.12      (![X51 : $i]:
% 5.88/6.12         (m1_subset_1 @ (k6_partfun1 @ X51) @ 
% 5.88/6.12          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X51)))),
% 5.88/6.12      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 5.88/6.12  thf('24', plain,
% 5.88/6.12      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 5.88/6.12         = (k6_partfun1 @ sk_A))),
% 5.88/6.12      inference('demod', [status(thm)], ['22', '23'])).
% 5.88/6.12  thf('25', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 5.88/6.12      inference('demod', [status(thm)], ['8', '9', '24'])).
% 5.88/6.12  thf(t45_relat_1, axiom,
% 5.88/6.12    (![A:$i]:
% 5.88/6.12     ( ( v1_relat_1 @ A ) =>
% 5.88/6.12       ( ![B:$i]:
% 5.88/6.12         ( ( v1_relat_1 @ B ) =>
% 5.88/6.12           ( r1_tarski @
% 5.88/6.12             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 5.88/6.12  thf('26', plain,
% 5.88/6.12      (![X20 : $i, X21 : $i]:
% 5.88/6.12         (~ (v1_relat_1 @ X20)
% 5.88/6.12          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X21 @ X20)) @ 
% 5.88/6.12             (k2_relat_1 @ X20))
% 5.88/6.12          | ~ (v1_relat_1 @ X21))),
% 5.88/6.12      inference('cnf', [status(esa)], [t45_relat_1])).
% 5.88/6.12  thf(d10_xboole_0, axiom,
% 5.88/6.12    (![A:$i,B:$i]:
% 5.88/6.12     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.88/6.12  thf('27', plain,
% 5.88/6.12      (![X1 : $i, X3 : $i]:
% 5.88/6.12         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 5.88/6.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.88/6.12  thf('28', plain,
% 5.88/6.12      (![X0 : $i, X1 : $i]:
% 5.88/6.12         (~ (v1_relat_1 @ X1)
% 5.88/6.12          | ~ (v1_relat_1 @ X0)
% 5.88/6.12          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 5.88/6.12               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 5.88/6.12          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 5.88/6.12      inference('sup-', [status(thm)], ['26', '27'])).
% 5.88/6.12  thf('29', plain,
% 5.88/6.12      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 5.88/6.12           (k2_relat_1 @ (k6_partfun1 @ sk_A)))
% 5.88/6.12        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)))
% 5.88/6.12        | ~ (v1_relat_1 @ sk_D)
% 5.88/6.12        | ~ (v1_relat_1 @ sk_C_1))),
% 5.88/6.12      inference('sup-', [status(thm)], ['25', '28'])).
% 5.88/6.12  thf(t71_relat_1, axiom,
% 5.88/6.12    (![A:$i]:
% 5.88/6.12     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 5.88/6.12       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 5.88/6.12  thf('30', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 5.88/6.12      inference('cnf', [status(esa)], [t71_relat_1])).
% 5.88/6.12  thf(redefinition_k6_partfun1, axiom,
% 5.88/6.12    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 5.88/6.12  thf('31', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 5.88/6.12      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.88/6.12  thf('32', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X23)) = (X23))),
% 5.88/6.12      inference('demod', [status(thm)], ['30', '31'])).
% 5.88/6.12  thf('33', plain,
% 5.88/6.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.88/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.88/6.12  thf(cc2_relset_1, axiom,
% 5.88/6.12    (![A:$i,B:$i,C:$i]:
% 5.88/6.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.88/6.12       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 5.88/6.12  thf('34', plain,
% 5.88/6.12      (![X29 : $i, X30 : $i, X31 : $i]:
% 5.88/6.12         ((v5_relat_1 @ X29 @ X31)
% 5.88/6.12          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 5.88/6.12      inference('cnf', [status(esa)], [cc2_relset_1])).
% 5.88/6.12  thf('35', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 5.88/6.12      inference('sup-', [status(thm)], ['33', '34'])).
% 5.88/6.12  thf(d19_relat_1, axiom,
% 5.88/6.12    (![A:$i,B:$i]:
% 5.88/6.12     ( ( v1_relat_1 @ B ) =>
% 5.88/6.12       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 5.88/6.12  thf('36', plain,
% 5.88/6.12      (![X15 : $i, X16 : $i]:
% 5.88/6.12         (~ (v5_relat_1 @ X15 @ X16)
% 5.88/6.12          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 5.88/6.12          | ~ (v1_relat_1 @ X15))),
% 5.88/6.12      inference('cnf', [status(esa)], [d19_relat_1])).
% 5.88/6.12  thf('37', plain,
% 5.88/6.12      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 5.88/6.12      inference('sup-', [status(thm)], ['35', '36'])).
% 5.88/6.12  thf('38', plain,
% 5.88/6.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.88/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.88/6.12  thf(cc2_relat_1, axiom,
% 5.88/6.12    (![A:$i]:
% 5.88/6.12     ( ( v1_relat_1 @ A ) =>
% 5.88/6.12       ( ![B:$i]:
% 5.88/6.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 5.88/6.12  thf('39', plain,
% 5.88/6.12      (![X13 : $i, X14 : $i]:
% 5.88/6.12         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 5.88/6.12          | (v1_relat_1 @ X13)
% 5.88/6.12          | ~ (v1_relat_1 @ X14))),
% 5.88/6.12      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.88/6.12  thf('40', plain,
% 5.88/6.12      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) | (v1_relat_1 @ sk_D))),
% 5.88/6.12      inference('sup-', [status(thm)], ['38', '39'])).
% 5.88/6.12  thf(fc6_relat_1, axiom,
% 5.88/6.12    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 5.88/6.12  thf('41', plain,
% 5.88/6.12      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 5.88/6.12      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.88/6.12  thf('42', plain, ((v1_relat_1 @ sk_D)),
% 5.88/6.12      inference('demod', [status(thm)], ['40', '41'])).
% 5.88/6.12  thf('43', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 5.88/6.12      inference('demod', [status(thm)], ['37', '42'])).
% 5.88/6.12  thf('44', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 5.88/6.12      inference('demod', [status(thm)], ['8', '9', '24'])).
% 5.88/6.12  thf('45', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X23)) = (X23))),
% 5.88/6.12      inference('demod', [status(thm)], ['30', '31'])).
% 5.88/6.12  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 5.88/6.12      inference('demod', [status(thm)], ['40', '41'])).
% 5.88/6.12  thf('47', plain,
% 5.88/6.12      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.88/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.88/6.12  thf('48', plain,
% 5.88/6.12      (![X13 : $i, X14 : $i]:
% 5.88/6.12         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 5.88/6.12          | (v1_relat_1 @ X13)
% 5.88/6.12          | ~ (v1_relat_1 @ X14))),
% 5.88/6.12      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.88/6.12  thf('49', plain,
% 5.88/6.12      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_1))),
% 5.88/6.12      inference('sup-', [status(thm)], ['47', '48'])).
% 5.88/6.12  thf('50', plain,
% 5.88/6.12      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 5.88/6.12      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.88/6.12  thf('51', plain, ((v1_relat_1 @ sk_C_1)),
% 5.88/6.12      inference('demod', [status(thm)], ['49', '50'])).
% 5.88/6.12  thf('52', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 5.88/6.12      inference('demod', [status(thm)],
% 5.88/6.12                ['29', '32', '43', '44', '45', '46', '51'])).
% 5.88/6.12  thf(d3_funct_2, axiom,
% 5.88/6.12    (![A:$i,B:$i]:
% 5.88/6.12     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 5.88/6.12       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 5.88/6.12  thf('53', plain,
% 5.88/6.12      (![X42 : $i, X43 : $i]:
% 5.88/6.12         (((k2_relat_1 @ X43) != (X42))
% 5.88/6.12          | (v2_funct_2 @ X43 @ X42)
% 5.88/6.12          | ~ (v5_relat_1 @ X43 @ X42)
% 5.88/6.12          | ~ (v1_relat_1 @ X43))),
% 5.88/6.12      inference('cnf', [status(esa)], [d3_funct_2])).
% 5.88/6.12  thf('54', plain,
% 5.88/6.12      (![X43 : $i]:
% 5.88/6.12         (~ (v1_relat_1 @ X43)
% 5.88/6.12          | ~ (v5_relat_1 @ X43 @ (k2_relat_1 @ X43))
% 5.88/6.12          | (v2_funct_2 @ X43 @ (k2_relat_1 @ X43)))),
% 5.88/6.12      inference('simplify', [status(thm)], ['53'])).
% 5.88/6.12  thf('55', plain,
% 5.88/6.12      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 5.88/6.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.88/6.12  thf('56', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 5.88/6.12      inference('simplify', [status(thm)], ['55'])).
% 5.88/6.12  thf('57', plain,
% 5.88/6.12      (![X15 : $i, X16 : $i]:
% 5.88/6.12         (~ (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 5.88/6.12          | (v5_relat_1 @ X15 @ X16)
% 5.88/6.12          | ~ (v1_relat_1 @ X15))),
% 5.88/6.12      inference('cnf', [status(esa)], [d19_relat_1])).
% 5.88/6.12  thf('58', plain,
% 5.88/6.12      (![X0 : $i]:
% 5.88/6.12         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 5.88/6.12      inference('sup-', [status(thm)], ['56', '57'])).
% 5.88/6.12  thf('59', plain,
% 5.88/6.12      (![X43 : $i]:
% 5.88/6.12         ((v2_funct_2 @ X43 @ (k2_relat_1 @ X43)) | ~ (v1_relat_1 @ X43))),
% 5.88/6.12      inference('clc', [status(thm)], ['54', '58'])).
% 5.88/6.12  thf('60', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 5.88/6.12      inference('sup+', [status(thm)], ['52', '59'])).
% 5.88/6.12  thf('61', plain, ((v1_relat_1 @ sk_D)),
% 5.88/6.12      inference('demod', [status(thm)], ['40', '41'])).
% 5.88/6.12  thf('62', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 5.88/6.12      inference('demod', [status(thm)], ['60', '61'])).
% 5.88/6.12  thf('63', plain,
% 5.88/6.12      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 5.88/6.12      inference('split', [status(esa)], ['0'])).
% 5.88/6.12  thf('64', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 5.88/6.12      inference('sup-', [status(thm)], ['62', '63'])).
% 5.88/6.12  thf('65', plain,
% 5.88/6.12      (~ ((v2_funct_1 @ sk_C_1)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 5.88/6.12      inference('split', [status(esa)], ['0'])).
% 5.88/6.12  thf('66', plain, (~ ((v2_funct_1 @ sk_C_1))),
% 5.88/6.12      inference('sat_resolution*', [status(thm)], ['64', '65'])).
% 5.88/6.12  thf('67', plain, (~ (v2_funct_1 @ sk_C_1)),
% 5.88/6.12      inference('simpl_trail', [status(thm)], ['1', '66'])).
% 5.88/6.12  thf('68', plain,
% 5.88/6.12      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.88/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.88/6.12  thf(l13_xboole_0, axiom,
% 5.88/6.12    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 5.88/6.12  thf('69', plain,
% 5.88/6.12      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 5.88/6.12      inference('cnf', [status(esa)], [l13_xboole_0])).
% 5.88/6.12  thf('70', plain,
% 5.88/6.12      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 5.88/6.12      inference('cnf', [status(esa)], [l13_xboole_0])).
% 5.88/6.12  thf(t4_subset_1, axiom,
% 5.88/6.12    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 5.88/6.12  thf('71', plain,
% 5.88/6.12      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 5.88/6.12      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.88/6.12  thf('72', plain,
% 5.88/6.12      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 5.88/6.12         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 5.88/6.12          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 5.88/6.12          | (r2_relset_1 @ X39 @ X40 @ X38 @ X41)
% 5.88/6.12          | ((X38) != (X41)))),
% 5.88/6.12      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.88/6.12  thf('73', plain,
% 5.88/6.12      (![X39 : $i, X40 : $i, X41 : $i]:
% 5.88/6.12         ((r2_relset_1 @ X39 @ X40 @ X41 @ X41)
% 5.88/6.12          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 5.88/6.12      inference('simplify', [status(thm)], ['72'])).
% 5.88/6.12  thf('74', plain,
% 5.88/6.12      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 5.88/6.12      inference('sup-', [status(thm)], ['71', '73'])).
% 5.88/6.12  thf('75', plain,
% 5.88/6.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.88/6.12         ((r2_relset_1 @ X2 @ X1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 5.88/6.12      inference('sup+', [status(thm)], ['70', '74'])).
% 5.88/6.12  thf(t113_zfmisc_1, axiom,
% 5.88/6.12    (![A:$i,B:$i]:
% 5.88/6.12     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 5.88/6.12       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 5.88/6.12  thf('76', plain,
% 5.88/6.12      (![X5 : $i, X6 : $i]:
% 5.88/6.12         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 5.88/6.12      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.88/6.12  thf('77', plain,
% 5.88/6.12      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 5.88/6.12      inference('simplify', [status(thm)], ['76'])).
% 5.88/6.12  thf('78', plain,
% 5.88/6.12      (![X51 : $i]:
% 5.88/6.12         (m1_subset_1 @ (k6_partfun1 @ X51) @ 
% 5.88/6.12          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X51)))),
% 5.88/6.12      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 5.88/6.12  thf('79', plain,
% 5.88/6.12      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 5.88/6.12         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 5.88/6.12          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 5.88/6.12          | ((X38) = (X41))
% 5.88/6.12          | ~ (r2_relset_1 @ X39 @ X40 @ X38 @ X41))),
% 5.88/6.12      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.88/6.12  thf('80', plain,
% 5.88/6.12      (![X0 : $i, X1 : $i]:
% 5.88/6.12         (~ (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 5.88/6.12          | ((k6_partfun1 @ X0) = (X1))
% 5.88/6.12          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 5.88/6.12      inference('sup-', [status(thm)], ['78', '79'])).
% 5.88/6.12  thf('81', plain,
% 5.88/6.12      (![X0 : $i]:
% 5.88/6.12         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 5.88/6.12          | ((k6_partfun1 @ k1_xboole_0) = (X0))
% 5.88/6.12          | ~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 5.88/6.12               (k6_partfun1 @ k1_xboole_0) @ X0))),
% 5.88/6.12      inference('sup-', [status(thm)], ['77', '80'])).
% 5.88/6.12  thf('82', plain,
% 5.88/6.12      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 5.88/6.12      inference('simplify', [status(thm)], ['76'])).
% 5.88/6.12  thf('83', plain,
% 5.88/6.12      (![X51 : $i]:
% 5.88/6.12         (m1_subset_1 @ (k6_partfun1 @ X51) @ 
% 5.88/6.12          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X51)))),
% 5.88/6.12      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 5.88/6.12  thf('84', plain,
% 5.88/6.12      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 5.88/6.12      inference('sup+', [status(thm)], ['82', '83'])).
% 5.88/6.12  thf('85', plain,
% 5.88/6.12      (![X5 : $i, X6 : $i]:
% 5.88/6.12         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 5.88/6.12      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.88/6.12  thf('86', plain,
% 5.88/6.12      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 5.88/6.12      inference('simplify', [status(thm)], ['85'])).
% 5.88/6.12  thf(cc3_relset_1, axiom,
% 5.88/6.12    (![A:$i,B:$i]:
% 5.88/6.12     ( ( v1_xboole_0 @ A ) =>
% 5.88/6.12       ( ![C:$i]:
% 5.88/6.12         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.88/6.12           ( v1_xboole_0 @ C ) ) ) ))).
% 5.88/6.12  thf('87', plain,
% 5.88/6.12      (![X32 : $i, X33 : $i, X34 : $i]:
% 5.88/6.12         (~ (v1_xboole_0 @ X32)
% 5.88/6.12          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X34)))
% 5.88/6.12          | (v1_xboole_0 @ X33))),
% 5.88/6.12      inference('cnf', [status(esa)], [cc3_relset_1])).
% 5.88/6.12  thf('88', plain,
% 5.88/6.12      (![X1 : $i]:
% 5.88/6.12         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 5.88/6.12          | (v1_xboole_0 @ X1)
% 5.88/6.12          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 5.88/6.12      inference('sup-', [status(thm)], ['86', '87'])).
% 5.88/6.12  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 5.88/6.12  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.88/6.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.88/6.12  thf('90', plain,
% 5.88/6.12      (![X1 : $i]:
% 5.88/6.12         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 5.88/6.12          | (v1_xboole_0 @ X1))),
% 5.88/6.12      inference('demod', [status(thm)], ['88', '89'])).
% 5.88/6.12  thf('91', plain, ((v1_xboole_0 @ (k6_partfun1 @ k1_xboole_0))),
% 5.88/6.12      inference('sup-', [status(thm)], ['84', '90'])).
% 5.88/6.12  thf('92', plain,
% 5.88/6.12      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 5.88/6.12      inference('cnf', [status(esa)], [l13_xboole_0])).
% 5.88/6.12  thf('93', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.88/6.12      inference('sup-', [status(thm)], ['91', '92'])).
% 5.88/6.12  thf('94', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.88/6.12      inference('sup-', [status(thm)], ['91', '92'])).
% 5.88/6.12  thf('95', plain,
% 5.88/6.12      (![X0 : $i]:
% 5.88/6.12         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 5.88/6.12          | ((k1_xboole_0) = (X0))
% 5.88/6.12          | ~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 5.88/6.12      inference('demod', [status(thm)], ['81', '93', '94'])).
% 5.88/6.12  thf('96', plain,
% 5.88/6.12      (![X0 : $i]:
% 5.88/6.12         (~ (v1_xboole_0 @ X0)
% 5.88/6.12          | ((k1_xboole_0) = (X0))
% 5.88/6.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 5.88/6.12      inference('sup-', [status(thm)], ['75', '95'])).
% 5.88/6.12  thf('97', plain,
% 5.88/6.12      (![X1 : $i]:
% 5.88/6.12         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 5.88/6.12          | (v1_xboole_0 @ X1))),
% 5.88/6.12      inference('demod', [status(thm)], ['88', '89'])).
% 5.88/6.12  thf('98', plain,
% 5.88/6.12      (![X0 : $i]:
% 5.88/6.12         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 5.88/6.12          | ((k1_xboole_0) = (X0)))),
% 5.88/6.12      inference('clc', [status(thm)], ['96', '97'])).
% 5.88/6.12  thf('99', plain,
% 5.88/6.12      (![X0 : $i, X1 : $i]:
% 5.88/6.12         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 5.88/6.12          | ~ (v1_xboole_0 @ X0)
% 5.88/6.12          | ((k1_xboole_0) = (X1)))),
% 5.88/6.12      inference('sup-', [status(thm)], ['69', '98'])).
% 5.88/6.12  thf('100', plain,
% 5.88/6.12      ((((k1_xboole_0) = (sk_C_1))
% 5.88/6.12        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.88/6.12      inference('sup-', [status(thm)], ['68', '99'])).
% 5.88/6.12  thf('101', plain,
% 5.88/6.12      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 5.88/6.12         = (k6_partfun1 @ sk_A))),
% 5.88/6.12      inference('demod', [status(thm)], ['22', '23'])).
% 5.88/6.12  thf('102', plain,
% 5.88/6.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.88/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.88/6.12  thf(t26_funct_2, axiom,
% 5.88/6.12    (![A:$i,B:$i,C:$i,D:$i]:
% 5.88/6.12     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.88/6.12         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.88/6.12       ( ![E:$i]:
% 5.88/6.12         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 5.88/6.12             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 5.88/6.12           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 5.88/6.12             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 5.88/6.12               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 5.88/6.12  thf('103', plain,
% 5.88/6.12      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 5.88/6.12         (~ (v1_funct_1 @ X59)
% 5.88/6.12          | ~ (v1_funct_2 @ X59 @ X60 @ X61)
% 5.88/6.12          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 5.88/6.12          | ~ (v2_funct_1 @ (k1_partfun1 @ X62 @ X60 @ X60 @ X61 @ X63 @ X59))
% 5.88/6.12          | (v2_funct_1 @ X63)
% 5.88/6.12          | ((X61) = (k1_xboole_0))
% 5.88/6.12          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X60)))
% 5.88/6.12          | ~ (v1_funct_2 @ X63 @ X62 @ X60)
% 5.88/6.12          | ~ (v1_funct_1 @ X63))),
% 5.88/6.12      inference('cnf', [status(esa)], [t26_funct_2])).
% 5.88/6.12  thf('104', plain,
% 5.88/6.12      (![X0 : $i, X1 : $i]:
% 5.88/6.12         (~ (v1_funct_1 @ X0)
% 5.88/6.12          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 5.88/6.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 5.88/6.12          | ((sk_A) = (k1_xboole_0))
% 5.88/6.12          | (v2_funct_1 @ X0)
% 5.88/6.12          | ~ (v2_funct_1 @ 
% 5.88/6.12               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 5.88/6.12          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 5.88/6.12          | ~ (v1_funct_1 @ sk_D))),
% 5.88/6.12      inference('sup-', [status(thm)], ['102', '103'])).
% 5.88/6.12  thf('105', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 5.88/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.88/6.12  thf('106', plain, ((v1_funct_1 @ sk_D)),
% 5.88/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.88/6.12  thf('107', plain,
% 5.88/6.12      (![X0 : $i, X1 : $i]:
% 5.88/6.12         (~ (v1_funct_1 @ X0)
% 5.88/6.12          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 5.88/6.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 5.88/6.12          | ((sk_A) = (k1_xboole_0))
% 5.88/6.12          | (v2_funct_1 @ X0)
% 5.88/6.12          | ~ (v2_funct_1 @ 
% 5.88/6.12               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 5.88/6.12      inference('demod', [status(thm)], ['104', '105', '106'])).
% 5.88/6.12  thf('108', plain,
% 5.88/6.12      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 5.88/6.12        | (v2_funct_1 @ sk_C_1)
% 5.88/6.12        | ((sk_A) = (k1_xboole_0))
% 5.88/6.12        | ~ (m1_subset_1 @ sk_C_1 @ 
% 5.88/6.12             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 5.88/6.12        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 5.88/6.12        | ~ (v1_funct_1 @ sk_C_1))),
% 5.88/6.12      inference('sup-', [status(thm)], ['101', '107'])).
% 5.88/6.12  thf(fc4_funct_1, axiom,
% 5.88/6.12    (![A:$i]:
% 5.88/6.12     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 5.88/6.12       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 5.88/6.12  thf('109', plain, (![X28 : $i]: (v2_funct_1 @ (k6_relat_1 @ X28))),
% 5.88/6.12      inference('cnf', [status(esa)], [fc4_funct_1])).
% 5.88/6.12  thf('110', plain, (![X58 : $i]: ((k6_partfun1 @ X58) = (k6_relat_1 @ X58))),
% 5.88/6.12      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.88/6.12  thf('111', plain, (![X28 : $i]: (v2_funct_1 @ (k6_partfun1 @ X28))),
% 5.88/6.12      inference('demod', [status(thm)], ['109', '110'])).
% 5.88/6.12  thf('112', plain,
% 5.88/6.12      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.88/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.88/6.12  thf('113', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 5.88/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.88/6.12  thf('114', plain, ((v1_funct_1 @ sk_C_1)),
% 5.88/6.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.88/6.12  thf('115', plain, (((v2_funct_1 @ sk_C_1) | ((sk_A) = (k1_xboole_0)))),
% 5.88/6.12      inference('demod', [status(thm)], ['108', '111', '112', '113', '114'])).
% 5.88/6.12  thf('116', plain, (~ (v2_funct_1 @ sk_C_1)),
% 5.88/6.12      inference('simpl_trail', [status(thm)], ['1', '66'])).
% 5.88/6.12  thf('117', plain, (((sk_A) = (k1_xboole_0))),
% 5.88/6.12      inference('clc', [status(thm)], ['115', '116'])).
% 5.88/6.12  thf('118', plain,
% 5.88/6.12      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 5.88/6.12      inference('simplify', [status(thm)], ['85'])).
% 5.88/6.12  thf('119', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.88/6.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.88/6.12  thf('120', plain, (((k1_xboole_0) = (sk_C_1))),
% 5.88/6.12      inference('demod', [status(thm)], ['100', '117', '118', '119'])).
% 5.88/6.12  thf('121', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.88/6.12      inference('sup-', [status(thm)], ['91', '92'])).
% 5.88/6.12  thf('122', plain, (![X28 : $i]: (v2_funct_1 @ (k6_partfun1 @ X28))),
% 5.88/6.12      inference('demod', [status(thm)], ['109', '110'])).
% 5.88/6.12  thf('123', plain, ((v2_funct_1 @ k1_xboole_0)),
% 5.88/6.12      inference('sup+', [status(thm)], ['121', '122'])).
% 5.88/6.12  thf('124', plain, ($false),
% 5.88/6.12      inference('demod', [status(thm)], ['67', '120', '123'])).
% 5.88/6.12  
% 5.88/6.12  % SZS output end Refutation
% 5.88/6.12  
% 5.88/6.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

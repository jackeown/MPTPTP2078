%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.exPWnQvQH4

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:48 EST 2020

% Result     : Theorem 10.53s
% Output     : Refutation 10.53s
% Verified   : 
% Statistics : Number of formulae       :  243 (6630 expanded)
%              Number of leaves         :   46 (2019 expanded)
%              Depth                    :   24
%              Number of atoms          : 2690 (143332 expanded)
%              Number of equality atoms :  102 (1793 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t76_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B )
              & ( v2_funct_1 @ B ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B )
                & ( v2_funct_1 @ B ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X57: $i,X58: $i] :
      ( ( ( k1_relset_1 @ X57 @ X57 @ X58 )
        = X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X57 ) ) )
      | ~ ( v1_funct_2 @ X58 @ X57 @ X57 )
      | ~ ( v1_funct_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('5',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','6','7','10'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X56: $i] :
      ( ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('13',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( v2_funct_1 @ X53 )
      | ( ( k2_relset_1 @ X55 @ X54 @ X53 )
       != X54 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X53 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) )
      | ~ ( v1_funct_2 @ X53 @ X55 @ X54 )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('20',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','6','7','10'])).

thf('23',plain,(
    ! [X56: $i] :
      ( ( v1_funct_2 @ X56 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('24',plain,
    ( ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','27','30','31'])).

thf('33',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ X9 @ ( k2_funct_1 @ X9 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('37',plain,(
    ! [X56: $i] :
      ( ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('38',plain,(
    ! [X56: $i] :
      ( ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('39',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X56: $i] :
      ( ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('45',plain,(
    ! [X56: $i] :
      ( ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('46',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v1_funct_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','6','7','10'])).

thf('57',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf('58',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf('61',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( v2_funct_1 @ X53 )
      | ( ( k2_relset_1 @ X55 @ X54 @ X53 )
       != X54 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X53 ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) )
      | ~ ( v1_funct_2 @ X53 @ X55 @ X54 )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('62',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('65',plain,
    ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('66',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63','64','65','66'])).

thf('68',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','57','58','59','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('71',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('72',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('73',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['69','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C )
        & ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) )).

thf('81',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( r2_relset_1 @ X44 @ X45 @ ( k4_relset_1 @ X44 @ X44 @ X44 @ X45 @ ( k6_partfun1 @ X44 ) @ X46 ) @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_funct_2])).

thf('82',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('83',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( r2_relset_1 @ X44 @ X45 @ ( k4_relset_1 @ X44 @ X44 @ X44 @ X45 @ ( k6_relat_1 @ X44 ) @ X46 ) @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('87',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k4_relset_1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22 )
        = ( k5_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['84','89'])).

thf('91',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','57','58','59','68'])).

thf('92',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('94',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ X3 @ X1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','98'])).

thf('100',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['69','78'])).

thf('101',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('102',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( X25 = X28 )
      | ~ ( r2_relset_1 @ X26 @ X27 @ X25 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['90','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['79','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
      = ( k5_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['108','113'])).

thf('115',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('119',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['120','125'])).

thf('127',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('130',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( X25 = X28 )
      | ~ ( r2_relset_1 @ X26 @ X27 @ X25 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['119','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['116','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ~ ( ( v2_funct_1 @ C )
            <=> ! [D: $i,E: $i] :
                  ( ( ( v1_funct_1 @ E )
                    & ( v1_funct_2 @ E @ D @ A )
                    & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) )
                 => ! [F: $i] :
                      ( ( ( v1_funct_1 @ F )
                        & ( v1_funct_2 @ F @ D @ A )
                        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) )
                     => ( ( r2_relset_1 @ D @ B @ ( k1_partfun1 @ D @ A @ A @ B @ E @ C ) @ ( k1_partfun1 @ D @ A @ A @ B @ F @ C ) )
                       => ( r2_relset_1 @ D @ A @ E @ F ) ) ) ) ) ) ) )).

thf('138',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X48 @ X47 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X48 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X48 ) ) )
      | ~ ( r2_relset_1 @ X51 @ X47 @ ( k1_partfun1 @ X51 @ X48 @ X48 @ X47 @ X50 @ X49 ) @ ( k1_partfun1 @ X51 @ X48 @ X48 @ X47 @ X52 @ X49 ) )
      | ( r2_relset_1 @ X51 @ X48 @ X50 @ X52 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X51 @ X48 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v2_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_2])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ( r2_relset_1 @ X1 @ sk_A @ X2 @ X0 )
      | ~ ( r2_relset_1 @ X1 @ sk_A @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B ) @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ sk_A )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ( r2_relset_1 @ X1 @ sk_A @ X2 @ X0 )
      | ~ ( r2_relset_1 @ X1 @ sk_A @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B ) @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ sk_A )
      | ~ ( v1_funct_1 @ X2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( r2_relset_1 @ X1 @ sk_A @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B ) @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ( r2_relset_1 @ X1 @ sk_A @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['136','144'])).

thf('146',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['145','146','147','148'])).

thf('150',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_relat_1 @ sk_A ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','149'])).

thf('151',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( r2_relset_1 @ X26 @ X27 @ X25 @ X28 )
      | ( X25 != X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('153',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_relset_1 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['151','153'])).

thf('155',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('156',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','57','58','59','68'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('157',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('158',plain,(
    ! [X56: $i] :
      ( ( v1_funct_2 @ X56 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('161',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ X0 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,(
    v1_funct_2 @ ( k6_relat_1 @ sk_A ) @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['156','162'])).

thf('164',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','57','58','59','68'])).

thf('165',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['150','154','155','163','164'])).

thf('166',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('167',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['165','166'])).

thf('168',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['165','166'])).

thf('169',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['165','166'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('170',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('171',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','167','168','169','170'])).

thf('172',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X57: $i,X58: $i] :
      ( ( ( k1_relset_1 @ X57 @ X57 @ X58 )
        = X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X57 ) ) )
      | ~ ( v1_funct_2 @ X58 @ X57 @ X57 )
      | ~ ( v1_funct_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('174',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('179',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['174','175','176','179'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('181',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
       != k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('182',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('185',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['182','185'])).

thf('187',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['165','166'])).

thf('188',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['188'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('190',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('191',plain,(
    ! [X1: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('192',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_relset_1 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    $false ),
    inference(demod,[status(thm)],['171','189','194'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.exPWnQvQH4
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:35:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 10.53/10.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.53/10.73  % Solved by: fo/fo7.sh
% 10.53/10.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.53/10.73  % done 11818 iterations in 10.260s
% 10.53/10.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.53/10.73  % SZS output start Refutation
% 10.53/10.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.53/10.73  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 10.53/10.73  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 10.53/10.73  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 10.53/10.73  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 10.53/10.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.53/10.73  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 10.53/10.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 10.53/10.73  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 10.53/10.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 10.53/10.73  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 10.53/10.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 10.53/10.73  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 10.53/10.73  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 10.53/10.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.53/10.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.53/10.73  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 10.53/10.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 10.53/10.73  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 10.53/10.73  thf(sk_C_type, type, sk_C: $i).
% 10.53/10.73  thf(sk_B_type, type, sk_B: $i).
% 10.53/10.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 10.53/10.73  thf(sk_A_type, type, sk_A: $i).
% 10.53/10.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 10.53/10.73  thf(t76_funct_2, conjecture,
% 10.53/10.73    (![A:$i,B:$i]:
% 10.53/10.73     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 10.53/10.73         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 10.53/10.73       ( ![C:$i]:
% 10.53/10.73         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 10.53/10.73             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 10.53/10.73           ( ( ( r2_relset_1 @
% 10.53/10.73                 A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 10.53/10.73               ( v2_funct_1 @ B ) ) =>
% 10.53/10.73             ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 10.53/10.73  thf(zf_stmt_0, negated_conjecture,
% 10.53/10.73    (~( ![A:$i,B:$i]:
% 10.53/10.73        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 10.53/10.73            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 10.53/10.73          ( ![C:$i]:
% 10.53/10.73            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 10.53/10.73                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 10.53/10.73              ( ( ( r2_relset_1 @
% 10.53/10.73                    A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 10.53/10.73                  ( v2_funct_1 @ B ) ) =>
% 10.53/10.73                ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 10.53/10.73    inference('cnf.neg', [status(esa)], [t76_funct_2])).
% 10.53/10.73  thf('0', plain,
% 10.53/10.73      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf(redefinition_k6_partfun1, axiom,
% 10.53/10.73    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 10.53/10.73  thf('1', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 10.53/10.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.53/10.73  thf('2', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))),
% 10.53/10.73      inference('demod', [status(thm)], ['0', '1'])).
% 10.53/10.73  thf('3', plain,
% 10.53/10.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf(t67_funct_2, axiom,
% 10.53/10.73    (![A:$i,B:$i]:
% 10.53/10.73     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 10.53/10.73         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 10.53/10.73       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 10.53/10.73  thf('4', plain,
% 10.53/10.73      (![X57 : $i, X58 : $i]:
% 10.53/10.73         (((k1_relset_1 @ X57 @ X57 @ X58) = (X57))
% 10.53/10.73          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X57)))
% 10.53/10.73          | ~ (v1_funct_2 @ X58 @ X57 @ X57)
% 10.53/10.73          | ~ (v1_funct_1 @ X58))),
% 10.53/10.73      inference('cnf', [status(esa)], [t67_funct_2])).
% 10.53/10.73  thf('5', plain,
% 10.53/10.73      ((~ (v1_funct_1 @ sk_B)
% 10.53/10.73        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 10.53/10.73        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 10.53/10.73      inference('sup-', [status(thm)], ['3', '4'])).
% 10.53/10.73  thf('6', plain, ((v1_funct_1 @ sk_B)),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf('7', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf('8', plain,
% 10.53/10.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf(redefinition_k1_relset_1, axiom,
% 10.53/10.73    (![A:$i,B:$i,C:$i]:
% 10.53/10.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.53/10.73       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 10.53/10.73  thf('9', plain,
% 10.53/10.73      (![X13 : $i, X14 : $i, X15 : $i]:
% 10.53/10.73         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 10.53/10.73          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 10.53/10.73      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 10.53/10.73  thf('10', plain,
% 10.53/10.73      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 10.53/10.73      inference('sup-', [status(thm)], ['8', '9'])).
% 10.53/10.73  thf('11', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 10.53/10.73      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 10.53/10.73  thf(t3_funct_2, axiom,
% 10.53/10.73    (![A:$i]:
% 10.53/10.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 10.53/10.73       ( ( v1_funct_1 @ A ) & 
% 10.53/10.73         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 10.53/10.73         ( m1_subset_1 @
% 10.53/10.73           A @ 
% 10.53/10.73           ( k1_zfmisc_1 @
% 10.53/10.73             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 10.53/10.73  thf('12', plain,
% 10.53/10.73      (![X56 : $i]:
% 10.53/10.73         ((m1_subset_1 @ X56 @ 
% 10.53/10.73           (k1_zfmisc_1 @ 
% 10.53/10.73            (k2_zfmisc_1 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))))
% 10.53/10.73          | ~ (v1_funct_1 @ X56)
% 10.53/10.73          | ~ (v1_relat_1 @ X56))),
% 10.53/10.73      inference('cnf', [status(esa)], [t3_funct_2])).
% 10.53/10.73  thf('13', plain,
% 10.53/10.73      (((m1_subset_1 @ sk_B @ 
% 10.53/10.73         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 10.53/10.73        | ~ (v1_relat_1 @ sk_B)
% 10.53/10.73        | ~ (v1_funct_1 @ sk_B))),
% 10.53/10.73      inference('sup+', [status(thm)], ['11', '12'])).
% 10.53/10.73  thf('14', plain,
% 10.53/10.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf(cc1_relset_1, axiom,
% 10.53/10.73    (![A:$i,B:$i,C:$i]:
% 10.53/10.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.53/10.73       ( v1_relat_1 @ C ) ))).
% 10.53/10.73  thf('15', plain,
% 10.53/10.73      (![X10 : $i, X11 : $i, X12 : $i]:
% 10.53/10.73         ((v1_relat_1 @ X10)
% 10.53/10.73          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 10.53/10.73      inference('cnf', [status(esa)], [cc1_relset_1])).
% 10.53/10.73  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 10.53/10.73      inference('sup-', [status(thm)], ['14', '15'])).
% 10.53/10.73  thf('17', plain, ((v1_funct_1 @ sk_B)),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf('18', plain,
% 10.53/10.73      ((m1_subset_1 @ sk_B @ 
% 10.53/10.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 10.53/10.73      inference('demod', [status(thm)], ['13', '16', '17'])).
% 10.53/10.73  thf(t31_funct_2, axiom,
% 10.53/10.73    (![A:$i,B:$i,C:$i]:
% 10.53/10.73     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.53/10.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.53/10.73       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 10.53/10.73         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 10.53/10.73           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 10.53/10.73           ( m1_subset_1 @
% 10.53/10.73             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 10.53/10.73  thf('19', plain,
% 10.53/10.73      (![X53 : $i, X54 : $i, X55 : $i]:
% 10.53/10.73         (~ (v2_funct_1 @ X53)
% 10.53/10.73          | ((k2_relset_1 @ X55 @ X54 @ X53) != (X54))
% 10.53/10.73          | (m1_subset_1 @ (k2_funct_1 @ X53) @ 
% 10.53/10.73             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55)))
% 10.53/10.73          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54)))
% 10.53/10.73          | ~ (v1_funct_2 @ X53 @ X55 @ X54)
% 10.53/10.73          | ~ (v1_funct_1 @ X53))),
% 10.53/10.73      inference('cnf', [status(esa)], [t31_funct_2])).
% 10.53/10.73  thf('20', plain,
% 10.53/10.73      ((~ (v1_funct_1 @ sk_B)
% 10.53/10.73        | ~ (v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 10.53/10.73        | (m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 10.53/10.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 10.53/10.73        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B)
% 10.53/10.73            != (k2_relat_1 @ sk_B))
% 10.53/10.73        | ~ (v2_funct_1 @ sk_B))),
% 10.53/10.73      inference('sup-', [status(thm)], ['18', '19'])).
% 10.53/10.73  thf('21', plain, ((v1_funct_1 @ sk_B)),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf('22', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 10.53/10.73      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 10.53/10.73  thf('23', plain,
% 10.53/10.73      (![X56 : $i]:
% 10.53/10.73         ((v1_funct_2 @ X56 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))
% 10.53/10.73          | ~ (v1_funct_1 @ X56)
% 10.53/10.73          | ~ (v1_relat_1 @ X56))),
% 10.53/10.73      inference('cnf', [status(esa)], [t3_funct_2])).
% 10.53/10.73  thf('24', plain,
% 10.53/10.73      (((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 10.53/10.73        | ~ (v1_relat_1 @ sk_B)
% 10.53/10.73        | ~ (v1_funct_1 @ sk_B))),
% 10.53/10.73      inference('sup+', [status(thm)], ['22', '23'])).
% 10.53/10.73  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 10.53/10.73      inference('sup-', [status(thm)], ['14', '15'])).
% 10.53/10.73  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf('27', plain, ((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))),
% 10.53/10.73      inference('demod', [status(thm)], ['24', '25', '26'])).
% 10.53/10.73  thf('28', plain,
% 10.53/10.73      ((m1_subset_1 @ sk_B @ 
% 10.53/10.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 10.53/10.73      inference('demod', [status(thm)], ['13', '16', '17'])).
% 10.53/10.73  thf(redefinition_k2_relset_1, axiom,
% 10.53/10.73    (![A:$i,B:$i,C:$i]:
% 10.53/10.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.53/10.73       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 10.53/10.73  thf('29', plain,
% 10.53/10.73      (![X16 : $i, X17 : $i, X18 : $i]:
% 10.53/10.73         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 10.53/10.73          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 10.53/10.73      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 10.53/10.73  thf('30', plain,
% 10.53/10.73      (((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B) = (k2_relat_1 @ sk_B))),
% 10.53/10.73      inference('sup-', [status(thm)], ['28', '29'])).
% 10.53/10.73  thf('31', plain, ((v2_funct_1 @ sk_B)),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf('32', plain,
% 10.53/10.73      (((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 10.53/10.73         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 10.53/10.73        | ((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B)))),
% 10.53/10.73      inference('demod', [status(thm)], ['20', '21', '27', '30', '31'])).
% 10.53/10.73  thf('33', plain,
% 10.53/10.73      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 10.53/10.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 10.53/10.73      inference('simplify', [status(thm)], ['32'])).
% 10.53/10.73  thf('34', plain,
% 10.53/10.73      (![X10 : $i, X11 : $i, X12 : $i]:
% 10.53/10.73         ((v1_relat_1 @ X10)
% 10.53/10.73          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 10.53/10.73      inference('cnf', [status(esa)], [cc1_relset_1])).
% 10.53/10.73  thf('35', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 10.53/10.73      inference('sup-', [status(thm)], ['33', '34'])).
% 10.53/10.73  thf(t61_funct_1, axiom,
% 10.53/10.73    (![A:$i]:
% 10.53/10.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 10.53/10.73       ( ( v2_funct_1 @ A ) =>
% 10.53/10.73         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 10.53/10.73             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 10.53/10.73           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 10.53/10.73             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 10.53/10.73  thf('36', plain,
% 10.53/10.73      (![X9 : $i]:
% 10.53/10.73         (~ (v2_funct_1 @ X9)
% 10.53/10.73          | ((k5_relat_1 @ X9 @ (k2_funct_1 @ X9))
% 10.53/10.73              = (k6_relat_1 @ (k1_relat_1 @ X9)))
% 10.53/10.73          | ~ (v1_funct_1 @ X9)
% 10.53/10.73          | ~ (v1_relat_1 @ X9))),
% 10.53/10.73      inference('cnf', [status(esa)], [t61_funct_1])).
% 10.53/10.73  thf('37', plain,
% 10.53/10.73      (![X56 : $i]:
% 10.53/10.73         ((m1_subset_1 @ X56 @ 
% 10.53/10.73           (k1_zfmisc_1 @ 
% 10.53/10.73            (k2_zfmisc_1 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))))
% 10.53/10.73          | ~ (v1_funct_1 @ X56)
% 10.53/10.73          | ~ (v1_relat_1 @ X56))),
% 10.53/10.73      inference('cnf', [status(esa)], [t3_funct_2])).
% 10.53/10.73  thf('38', plain,
% 10.53/10.73      (![X56 : $i]:
% 10.53/10.73         ((m1_subset_1 @ X56 @ 
% 10.53/10.73           (k1_zfmisc_1 @ 
% 10.53/10.73            (k2_zfmisc_1 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))))
% 10.53/10.73          | ~ (v1_funct_1 @ X56)
% 10.53/10.73          | ~ (v1_relat_1 @ X56))),
% 10.53/10.73      inference('cnf', [status(esa)], [t3_funct_2])).
% 10.53/10.73  thf(redefinition_k1_partfun1, axiom,
% 10.53/10.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 10.53/10.73     ( ( ( v1_funct_1 @ E ) & 
% 10.53/10.73         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.53/10.73         ( v1_funct_1 @ F ) & 
% 10.53/10.73         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 10.53/10.73       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 10.53/10.73  thf('39', plain,
% 10.53/10.73      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 10.53/10.73         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 10.53/10.73          | ~ (v1_funct_1 @ X37)
% 10.53/10.73          | ~ (v1_funct_1 @ X40)
% 10.53/10.73          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 10.53/10.73          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 10.53/10.73              = (k5_relat_1 @ X37 @ X40)))),
% 10.53/10.73      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 10.53/10.73  thf('40', plain,
% 10.53/10.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.53/10.73         (~ (v1_relat_1 @ X0)
% 10.53/10.73          | ~ (v1_funct_1 @ X0)
% 10.53/10.73          | ((k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 10.53/10.73              X0 @ X1) = (k5_relat_1 @ X0 @ X1))
% 10.53/10.73          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 10.53/10.73          | ~ (v1_funct_1 @ X1)
% 10.53/10.73          | ~ (v1_funct_1 @ X0))),
% 10.53/10.73      inference('sup-', [status(thm)], ['38', '39'])).
% 10.53/10.73  thf('41', plain,
% 10.53/10.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.53/10.73         (~ (v1_funct_1 @ X1)
% 10.53/10.73          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 10.53/10.73          | ((k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 10.53/10.73              X0 @ X1) = (k5_relat_1 @ X0 @ X1))
% 10.53/10.73          | ~ (v1_funct_1 @ X0)
% 10.53/10.73          | ~ (v1_relat_1 @ X0))),
% 10.53/10.73      inference('simplify', [status(thm)], ['40'])).
% 10.53/10.73  thf('42', plain,
% 10.53/10.73      (![X0 : $i, X1 : $i]:
% 10.53/10.73         (~ (v1_relat_1 @ X0)
% 10.53/10.73          | ~ (v1_funct_1 @ X0)
% 10.53/10.73          | ~ (v1_relat_1 @ X1)
% 10.53/10.73          | ~ (v1_funct_1 @ X1)
% 10.53/10.73          | ((k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 10.53/10.73              (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0)
% 10.53/10.73              = (k5_relat_1 @ X1 @ X0))
% 10.53/10.73          | ~ (v1_funct_1 @ X0))),
% 10.53/10.73      inference('sup-', [status(thm)], ['37', '41'])).
% 10.53/10.73  thf('43', plain,
% 10.53/10.73      (![X0 : $i, X1 : $i]:
% 10.53/10.73         (((k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 10.53/10.73            (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0)
% 10.53/10.73            = (k5_relat_1 @ X1 @ X0))
% 10.53/10.73          | ~ (v1_funct_1 @ X1)
% 10.53/10.73          | ~ (v1_relat_1 @ X1)
% 10.53/10.73          | ~ (v1_funct_1 @ X0)
% 10.53/10.73          | ~ (v1_relat_1 @ X0))),
% 10.53/10.73      inference('simplify', [status(thm)], ['42'])).
% 10.53/10.73  thf('44', plain,
% 10.53/10.73      (![X56 : $i]:
% 10.53/10.73         ((m1_subset_1 @ X56 @ 
% 10.53/10.73           (k1_zfmisc_1 @ 
% 10.53/10.73            (k2_zfmisc_1 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))))
% 10.53/10.73          | ~ (v1_funct_1 @ X56)
% 10.53/10.73          | ~ (v1_relat_1 @ X56))),
% 10.53/10.73      inference('cnf', [status(esa)], [t3_funct_2])).
% 10.53/10.73  thf('45', plain,
% 10.53/10.73      (![X56 : $i]:
% 10.53/10.73         ((m1_subset_1 @ X56 @ 
% 10.53/10.73           (k1_zfmisc_1 @ 
% 10.53/10.73            (k2_zfmisc_1 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))))
% 10.53/10.73          | ~ (v1_funct_1 @ X56)
% 10.53/10.73          | ~ (v1_relat_1 @ X56))),
% 10.53/10.73      inference('cnf', [status(esa)], [t3_funct_2])).
% 10.53/10.73  thf(dt_k1_partfun1, axiom,
% 10.53/10.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 10.53/10.73     ( ( ( v1_funct_1 @ E ) & 
% 10.53/10.73         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.53/10.73         ( v1_funct_1 @ F ) & 
% 10.53/10.73         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 10.53/10.73       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 10.53/10.73         ( m1_subset_1 @
% 10.53/10.73           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 10.53/10.73           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 10.53/10.73  thf('46', plain,
% 10.53/10.73      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 10.53/10.73         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 10.53/10.73          | ~ (v1_funct_1 @ X29)
% 10.53/10.73          | ~ (v1_funct_1 @ X32)
% 10.53/10.73          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 10.53/10.73          | (v1_funct_1 @ (k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)))),
% 10.53/10.73      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 10.53/10.73  thf('47', plain,
% 10.53/10.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.53/10.73         (~ (v1_relat_1 @ X0)
% 10.53/10.73          | ~ (v1_funct_1 @ X0)
% 10.53/10.73          | (v1_funct_1 @ 
% 10.53/10.73             (k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 10.53/10.73              X0 @ X1))
% 10.53/10.73          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 10.53/10.73          | ~ (v1_funct_1 @ X1)
% 10.53/10.73          | ~ (v1_funct_1 @ X0))),
% 10.53/10.73      inference('sup-', [status(thm)], ['45', '46'])).
% 10.53/10.73  thf('48', plain,
% 10.53/10.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.53/10.73         (~ (v1_funct_1 @ X1)
% 10.53/10.73          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 10.53/10.73          | (v1_funct_1 @ 
% 10.53/10.73             (k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 10.53/10.73              X0 @ X1))
% 10.53/10.73          | ~ (v1_funct_1 @ X0)
% 10.53/10.73          | ~ (v1_relat_1 @ X0))),
% 10.53/10.73      inference('simplify', [status(thm)], ['47'])).
% 10.53/10.73  thf('49', plain,
% 10.53/10.73      (![X0 : $i, X1 : $i]:
% 10.53/10.73         (~ (v1_relat_1 @ X0)
% 10.53/10.73          | ~ (v1_funct_1 @ X0)
% 10.53/10.73          | ~ (v1_relat_1 @ X1)
% 10.53/10.73          | ~ (v1_funct_1 @ X1)
% 10.53/10.73          | (v1_funct_1 @ 
% 10.53/10.73             (k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 10.53/10.73              (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0))
% 10.53/10.73          | ~ (v1_funct_1 @ X0))),
% 10.53/10.73      inference('sup-', [status(thm)], ['44', '48'])).
% 10.53/10.73  thf('50', plain,
% 10.53/10.73      (![X0 : $i, X1 : $i]:
% 10.53/10.73         ((v1_funct_1 @ 
% 10.53/10.73           (k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 10.53/10.73            (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0))
% 10.53/10.73          | ~ (v1_funct_1 @ X1)
% 10.53/10.73          | ~ (v1_relat_1 @ X1)
% 10.53/10.73          | ~ (v1_funct_1 @ X0)
% 10.53/10.73          | ~ (v1_relat_1 @ X0))),
% 10.53/10.73      inference('simplify', [status(thm)], ['49'])).
% 10.53/10.73  thf('51', plain,
% 10.53/10.73      (![X0 : $i, X1 : $i]:
% 10.53/10.73         ((v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 10.53/10.73          | ~ (v1_relat_1 @ X0)
% 10.53/10.73          | ~ (v1_funct_1 @ X0)
% 10.53/10.73          | ~ (v1_relat_1 @ X1)
% 10.53/10.73          | ~ (v1_funct_1 @ X1)
% 10.53/10.73          | ~ (v1_relat_1 @ X0)
% 10.53/10.73          | ~ (v1_funct_1 @ X0)
% 10.53/10.73          | ~ (v1_relat_1 @ X1)
% 10.53/10.73          | ~ (v1_funct_1 @ X1))),
% 10.53/10.73      inference('sup+', [status(thm)], ['43', '50'])).
% 10.53/10.73  thf('52', plain,
% 10.53/10.73      (![X0 : $i, X1 : $i]:
% 10.53/10.73         (~ (v1_funct_1 @ X1)
% 10.53/10.73          | ~ (v1_relat_1 @ X1)
% 10.53/10.73          | ~ (v1_funct_1 @ X0)
% 10.53/10.73          | ~ (v1_relat_1 @ X0)
% 10.53/10.73          | (v1_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 10.53/10.73      inference('simplify', [status(thm)], ['51'])).
% 10.53/10.73  thf('53', plain,
% 10.53/10.73      (![X0 : $i]:
% 10.53/10.73         ((v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 10.53/10.73          | ~ (v1_relat_1 @ X0)
% 10.53/10.73          | ~ (v1_funct_1 @ X0)
% 10.53/10.73          | ~ (v2_funct_1 @ X0)
% 10.53/10.73          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 10.53/10.73          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 10.53/10.73          | ~ (v1_relat_1 @ X0)
% 10.53/10.73          | ~ (v1_funct_1 @ X0))),
% 10.53/10.73      inference('sup+', [status(thm)], ['36', '52'])).
% 10.53/10.73  thf('54', plain,
% 10.53/10.73      (![X0 : $i]:
% 10.53/10.73         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 10.53/10.73          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 10.53/10.73          | ~ (v2_funct_1 @ X0)
% 10.53/10.73          | ~ (v1_funct_1 @ X0)
% 10.53/10.73          | ~ (v1_relat_1 @ X0)
% 10.53/10.73          | (v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 10.53/10.73      inference('simplify', [status(thm)], ['53'])).
% 10.53/10.73  thf('55', plain,
% 10.53/10.73      (((v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 10.53/10.73        | ~ (v1_relat_1 @ sk_B)
% 10.53/10.73        | ~ (v1_funct_1 @ sk_B)
% 10.53/10.73        | ~ (v2_funct_1 @ sk_B)
% 10.53/10.73        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 10.53/10.73      inference('sup-', [status(thm)], ['35', '54'])).
% 10.53/10.73  thf('56', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 10.53/10.73      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 10.53/10.73  thf('57', plain, ((v1_relat_1 @ sk_B)),
% 10.53/10.73      inference('sup-', [status(thm)], ['14', '15'])).
% 10.53/10.73  thf('58', plain, ((v1_funct_1 @ sk_B)),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf('59', plain, ((v2_funct_1 @ sk_B)),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf('60', plain,
% 10.53/10.73      ((m1_subset_1 @ sk_B @ 
% 10.53/10.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 10.53/10.73      inference('demod', [status(thm)], ['13', '16', '17'])).
% 10.53/10.73  thf('61', plain,
% 10.53/10.73      (![X53 : $i, X54 : $i, X55 : $i]:
% 10.53/10.73         (~ (v2_funct_1 @ X53)
% 10.53/10.73          | ((k2_relset_1 @ X55 @ X54 @ X53) != (X54))
% 10.53/10.73          | (v1_funct_1 @ (k2_funct_1 @ X53))
% 10.53/10.73          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54)))
% 10.53/10.73          | ~ (v1_funct_2 @ X53 @ X55 @ X54)
% 10.53/10.73          | ~ (v1_funct_1 @ X53))),
% 10.53/10.73      inference('cnf', [status(esa)], [t31_funct_2])).
% 10.53/10.73  thf('62', plain,
% 10.53/10.73      ((~ (v1_funct_1 @ sk_B)
% 10.53/10.73        | ~ (v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 10.53/10.73        | (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 10.53/10.73        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B)
% 10.53/10.73            != (k2_relat_1 @ sk_B))
% 10.53/10.73        | ~ (v2_funct_1 @ sk_B))),
% 10.53/10.73      inference('sup-', [status(thm)], ['60', '61'])).
% 10.53/10.73  thf('63', plain, ((v1_funct_1 @ sk_B)),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf('64', plain, ((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))),
% 10.53/10.73      inference('demod', [status(thm)], ['24', '25', '26'])).
% 10.53/10.73  thf('65', plain,
% 10.53/10.73      (((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B) = (k2_relat_1 @ sk_B))),
% 10.53/10.73      inference('sup-', [status(thm)], ['28', '29'])).
% 10.53/10.73  thf('66', plain, ((v2_funct_1 @ sk_B)),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf('67', plain,
% 10.53/10.73      (((v1_funct_1 @ (k2_funct_1 @ sk_B))
% 10.53/10.73        | ((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B)))),
% 10.53/10.73      inference('demod', [status(thm)], ['62', '63', '64', '65', '66'])).
% 10.53/10.73  thf('68', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 10.53/10.73      inference('simplify', [status(thm)], ['67'])).
% 10.53/10.73  thf('69', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 10.53/10.73      inference('demod', [status(thm)], ['55', '56', '57', '58', '59', '68'])).
% 10.53/10.73  thf('70', plain,
% 10.53/10.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf(dt_k6_partfun1, axiom,
% 10.53/10.73    (![A:$i]:
% 10.53/10.73     ( ( m1_subset_1 @
% 10.53/10.73         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 10.53/10.73       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 10.53/10.73  thf('71', plain,
% 10.53/10.73      (![X36 : $i]:
% 10.53/10.73         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 10.53/10.73          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 10.53/10.73      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 10.53/10.73  thf('72', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 10.53/10.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.53/10.73  thf('73', plain,
% 10.53/10.73      (![X36 : $i]:
% 10.53/10.73         (m1_subset_1 @ (k6_relat_1 @ X36) @ 
% 10.53/10.73          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 10.53/10.73      inference('demod', [status(thm)], ['71', '72'])).
% 10.53/10.73  thf('74', plain,
% 10.53/10.73      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 10.53/10.73         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 10.53/10.73          | ~ (v1_funct_1 @ X37)
% 10.53/10.73          | ~ (v1_funct_1 @ X40)
% 10.53/10.73          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 10.53/10.73          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 10.53/10.73              = (k5_relat_1 @ X37 @ X40)))),
% 10.53/10.73      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 10.53/10.73  thf('75', plain,
% 10.53/10.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.53/10.73         (((k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 10.53/10.73            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 10.53/10.73          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 10.53/10.73          | ~ (v1_funct_1 @ X1)
% 10.53/10.73          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 10.53/10.73      inference('sup-', [status(thm)], ['73', '74'])).
% 10.53/10.73  thf('76', plain,
% 10.53/10.73      (![X0 : $i]:
% 10.53/10.73         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 10.53/10.73          | ~ (v1_funct_1 @ sk_B)
% 10.53/10.73          | ((k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B)
% 10.53/10.73              = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B)))),
% 10.53/10.73      inference('sup-', [status(thm)], ['70', '75'])).
% 10.53/10.73  thf('77', plain, ((v1_funct_1 @ sk_B)),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf('78', plain,
% 10.53/10.73      (![X0 : $i]:
% 10.53/10.73         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 10.53/10.73          | ((k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B)
% 10.53/10.73              = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B)))),
% 10.53/10.73      inference('demod', [status(thm)], ['76', '77'])).
% 10.53/10.73  thf('79', plain,
% 10.53/10.73      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 10.53/10.73         = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 10.53/10.73      inference('sup-', [status(thm)], ['69', '78'])).
% 10.53/10.73  thf('80', plain,
% 10.53/10.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf(t23_funct_2, axiom,
% 10.53/10.73    (![A:$i,B:$i,C:$i]:
% 10.53/10.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.53/10.73       ( ( r2_relset_1 @
% 10.53/10.73           A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ 
% 10.53/10.73           C ) & 
% 10.53/10.73         ( r2_relset_1 @
% 10.53/10.73           A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ 
% 10.53/10.73           C ) ) ))).
% 10.53/10.73  thf('81', plain,
% 10.53/10.73      (![X44 : $i, X45 : $i, X46 : $i]:
% 10.53/10.73         ((r2_relset_1 @ X44 @ X45 @ 
% 10.53/10.73           (k4_relset_1 @ X44 @ X44 @ X44 @ X45 @ (k6_partfun1 @ X44) @ X46) @ 
% 10.53/10.73           X46)
% 10.53/10.73          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 10.53/10.73      inference('cnf', [status(esa)], [t23_funct_2])).
% 10.53/10.73  thf('82', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 10.53/10.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.53/10.73  thf('83', plain,
% 10.53/10.73      (![X44 : $i, X45 : $i, X46 : $i]:
% 10.53/10.73         ((r2_relset_1 @ X44 @ X45 @ 
% 10.53/10.73           (k4_relset_1 @ X44 @ X44 @ X44 @ X45 @ (k6_relat_1 @ X44) @ X46) @ 
% 10.53/10.73           X46)
% 10.53/10.73          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 10.53/10.73      inference('demod', [status(thm)], ['81', '82'])).
% 10.53/10.73  thf('84', plain,
% 10.53/10.73      ((r2_relset_1 @ sk_A @ sk_A @ 
% 10.53/10.73        (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 10.53/10.73        sk_B)),
% 10.53/10.73      inference('sup-', [status(thm)], ['80', '83'])).
% 10.53/10.73  thf('85', plain,
% 10.53/10.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf('86', plain,
% 10.53/10.73      (![X36 : $i]:
% 10.53/10.73         (m1_subset_1 @ (k6_relat_1 @ X36) @ 
% 10.53/10.73          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 10.53/10.73      inference('demod', [status(thm)], ['71', '72'])).
% 10.53/10.73  thf(redefinition_k4_relset_1, axiom,
% 10.53/10.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 10.53/10.73     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.53/10.73         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 10.53/10.73       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 10.53/10.73  thf('87', plain,
% 10.53/10.73      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 10.53/10.73         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 10.53/10.73          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 10.53/10.73          | ((k4_relset_1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22)
% 10.53/10.73              = (k5_relat_1 @ X19 @ X22)))),
% 10.53/10.73      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 10.53/10.73  thf('88', plain,
% 10.53/10.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.53/10.73         (((k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 10.53/10.73            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 10.53/10.73          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2))))),
% 10.53/10.73      inference('sup-', [status(thm)], ['86', '87'])).
% 10.53/10.73  thf('89', plain,
% 10.53/10.73      (![X0 : $i]:
% 10.53/10.73         ((k4_relset_1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B)
% 10.53/10.73           = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))),
% 10.53/10.73      inference('sup-', [status(thm)], ['85', '88'])).
% 10.53/10.73  thf('90', plain,
% 10.53/10.73      ((r2_relset_1 @ sk_A @ sk_A @ 
% 10.53/10.73        (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ sk_B)),
% 10.53/10.73      inference('demod', [status(thm)], ['84', '89'])).
% 10.53/10.73  thf('91', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 10.53/10.73      inference('demod', [status(thm)], ['55', '56', '57', '58', '59', '68'])).
% 10.53/10.73  thf('92', plain,
% 10.53/10.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf('93', plain,
% 10.53/10.73      (![X36 : $i]:
% 10.53/10.73         (m1_subset_1 @ (k6_relat_1 @ X36) @ 
% 10.53/10.73          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 10.53/10.73      inference('demod', [status(thm)], ['71', '72'])).
% 10.53/10.73  thf('94', plain,
% 10.53/10.73      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 10.53/10.73         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 10.53/10.73          | ~ (v1_funct_1 @ X29)
% 10.53/10.73          | ~ (v1_funct_1 @ X32)
% 10.53/10.73          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 10.53/10.73          | (m1_subset_1 @ (k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32) @ 
% 10.53/10.73             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X34))))),
% 10.53/10.73      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 10.53/10.73  thf('95', plain,
% 10.53/10.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.53/10.73         ((m1_subset_1 @ 
% 10.53/10.73           (k1_partfun1 @ X0 @ X0 @ X3 @ X1 @ (k6_relat_1 @ X0) @ X2) @ 
% 10.53/10.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 10.53/10.73          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 10.53/10.73          | ~ (v1_funct_1 @ X2)
% 10.53/10.73          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 10.53/10.73      inference('sup-', [status(thm)], ['93', '94'])).
% 10.53/10.73  thf('96', plain,
% 10.53/10.73      (![X0 : $i]:
% 10.53/10.73         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 10.53/10.73          | ~ (v1_funct_1 @ sk_B)
% 10.53/10.73          | (m1_subset_1 @ 
% 10.53/10.73             (k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B) @ 
% 10.53/10.73             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A))))),
% 10.53/10.73      inference('sup-', [status(thm)], ['92', '95'])).
% 10.53/10.73  thf('97', plain, ((v1_funct_1 @ sk_B)),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf('98', plain,
% 10.53/10.73      (![X0 : $i]:
% 10.53/10.73         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 10.53/10.73          | (m1_subset_1 @ 
% 10.53/10.73             (k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B) @ 
% 10.53/10.73             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A))))),
% 10.53/10.73      inference('demod', [status(thm)], ['96', '97'])).
% 10.53/10.73  thf('99', plain,
% 10.53/10.73      ((m1_subset_1 @ 
% 10.53/10.73        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 10.53/10.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.73      inference('sup-', [status(thm)], ['91', '98'])).
% 10.53/10.73  thf('100', plain,
% 10.53/10.73      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 10.53/10.73         = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 10.53/10.73      inference('sup-', [status(thm)], ['69', '78'])).
% 10.53/10.73  thf('101', plain,
% 10.53/10.73      ((m1_subset_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 10.53/10.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.73      inference('demod', [status(thm)], ['99', '100'])).
% 10.53/10.73  thf(redefinition_r2_relset_1, axiom,
% 10.53/10.73    (![A:$i,B:$i,C:$i,D:$i]:
% 10.53/10.73     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.53/10.73         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.53/10.73       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 10.53/10.73  thf('102', plain,
% 10.53/10.73      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 10.53/10.73         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 10.53/10.73          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 10.53/10.73          | ((X25) = (X28))
% 10.53/10.73          | ~ (r2_relset_1 @ X26 @ X27 @ X25 @ X28))),
% 10.53/10.73      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 10.53/10.73  thf('103', plain,
% 10.53/10.73      (![X0 : $i]:
% 10.53/10.73         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 10.53/10.73             (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ X0)
% 10.53/10.73          | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (X0))
% 10.53/10.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 10.53/10.73      inference('sup-', [status(thm)], ['101', '102'])).
% 10.53/10.73  thf('104', plain,
% 10.53/10.73      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 10.53/10.73        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B)))),
% 10.53/10.73      inference('sup-', [status(thm)], ['90', '103'])).
% 10.53/10.73  thf('105', plain,
% 10.53/10.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf('106', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))),
% 10.53/10.73      inference('demod', [status(thm)], ['104', '105'])).
% 10.53/10.73  thf('107', plain,
% 10.53/10.73      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 10.53/10.73         = (sk_B))),
% 10.53/10.73      inference('demod', [status(thm)], ['79', '106'])).
% 10.53/10.73  thf('108', plain,
% 10.53/10.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf('109', plain,
% 10.53/10.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf('110', plain,
% 10.53/10.73      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 10.53/10.73         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 10.53/10.73          | ~ (v1_funct_1 @ X37)
% 10.53/10.73          | ~ (v1_funct_1 @ X40)
% 10.53/10.73          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 10.53/10.73          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 10.53/10.73              = (k5_relat_1 @ X37 @ X40)))),
% 10.53/10.73      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 10.53/10.73  thf('111', plain,
% 10.53/10.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.73         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 10.53/10.73            = (k5_relat_1 @ sk_C @ X0))
% 10.53/10.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 10.53/10.73          | ~ (v1_funct_1 @ X0)
% 10.53/10.73          | ~ (v1_funct_1 @ sk_C))),
% 10.53/10.73      inference('sup-', [status(thm)], ['109', '110'])).
% 10.53/10.73  thf('112', plain, ((v1_funct_1 @ sk_C)),
% 10.53/10.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.73  thf('113', plain,
% 10.53/10.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.73         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 10.53/10.73            = (k5_relat_1 @ sk_C @ X0))
% 10.53/10.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 10.53/10.73          | ~ (v1_funct_1 @ X0))),
% 10.53/10.73      inference('demod', [status(thm)], ['111', '112'])).
% 10.53/10.73  thf('114', plain,
% 10.53/10.73      ((~ (v1_funct_1 @ sk_B)
% 10.53/10.74        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 10.53/10.74            = (k5_relat_1 @ sk_C @ sk_B)))),
% 10.53/10.74      inference('sup-', [status(thm)], ['108', '113'])).
% 10.53/10.74  thf('115', plain, ((v1_funct_1 @ sk_B)),
% 10.53/10.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.74  thf('116', plain,
% 10.53/10.74      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 10.53/10.74         = (k5_relat_1 @ sk_C @ sk_B))),
% 10.53/10.74      inference('demod', [status(thm)], ['114', '115'])).
% 10.53/10.74  thf('117', plain,
% 10.53/10.74      ((r2_relset_1 @ sk_A @ sk_A @ 
% 10.53/10.74        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ sk_B)),
% 10.53/10.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.74  thf('118', plain,
% 10.53/10.74      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 10.53/10.74         = (k5_relat_1 @ sk_C @ sk_B))),
% 10.53/10.74      inference('demod', [status(thm)], ['114', '115'])).
% 10.53/10.74  thf('119', plain,
% 10.53/10.74      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ sk_B)),
% 10.53/10.74      inference('demod', [status(thm)], ['117', '118'])).
% 10.53/10.74  thf('120', plain,
% 10.53/10.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.74  thf('121', plain,
% 10.53/10.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.74  thf('122', plain,
% 10.53/10.74      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 10.53/10.74         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 10.53/10.74          | ~ (v1_funct_1 @ X29)
% 10.53/10.74          | ~ (v1_funct_1 @ X32)
% 10.53/10.74          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 10.53/10.74          | (m1_subset_1 @ (k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32) @ 
% 10.53/10.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X34))))),
% 10.53/10.74      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 10.53/10.74  thf('123', plain,
% 10.53/10.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.74         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 10.53/10.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 10.53/10.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 10.53/10.74          | ~ (v1_funct_1 @ X1)
% 10.53/10.74          | ~ (v1_funct_1 @ sk_C))),
% 10.53/10.74      inference('sup-', [status(thm)], ['121', '122'])).
% 10.53/10.74  thf('124', plain, ((v1_funct_1 @ sk_C)),
% 10.53/10.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.74  thf('125', plain,
% 10.53/10.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.74         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 10.53/10.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 10.53/10.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 10.53/10.74          | ~ (v1_funct_1 @ X1))),
% 10.53/10.74      inference('demod', [status(thm)], ['123', '124'])).
% 10.53/10.74  thf('126', plain,
% 10.53/10.74      ((~ (v1_funct_1 @ sk_B)
% 10.53/10.74        | (m1_subset_1 @ 
% 10.53/10.74           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 10.53/10.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 10.53/10.74      inference('sup-', [status(thm)], ['120', '125'])).
% 10.53/10.74  thf('127', plain, ((v1_funct_1 @ sk_B)),
% 10.53/10.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.74  thf('128', plain,
% 10.53/10.74      ((m1_subset_1 @ 
% 10.53/10.74        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 10.53/10.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.74      inference('demod', [status(thm)], ['126', '127'])).
% 10.53/10.74  thf('129', plain,
% 10.53/10.74      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 10.53/10.74         = (k5_relat_1 @ sk_C @ sk_B))),
% 10.53/10.74      inference('demod', [status(thm)], ['114', '115'])).
% 10.53/10.74  thf('130', plain,
% 10.53/10.74      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_B) @ 
% 10.53/10.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.74      inference('demod', [status(thm)], ['128', '129'])).
% 10.53/10.74  thf('131', plain,
% 10.53/10.74      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 10.53/10.74         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 10.53/10.74          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 10.53/10.74          | ((X25) = (X28))
% 10.53/10.74          | ~ (r2_relset_1 @ X26 @ X27 @ X25 @ X28))),
% 10.53/10.74      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 10.53/10.74  thf('132', plain,
% 10.53/10.74      (![X0 : $i]:
% 10.53/10.74         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ X0)
% 10.53/10.74          | ((k5_relat_1 @ sk_C @ sk_B) = (X0))
% 10.53/10.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 10.53/10.74      inference('sup-', [status(thm)], ['130', '131'])).
% 10.53/10.74  thf('133', plain,
% 10.53/10.74      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 10.53/10.74        | ((k5_relat_1 @ sk_C @ sk_B) = (sk_B)))),
% 10.53/10.74      inference('sup-', [status(thm)], ['119', '132'])).
% 10.53/10.74  thf('134', plain,
% 10.53/10.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.74  thf('135', plain, (((k5_relat_1 @ sk_C @ sk_B) = (sk_B))),
% 10.53/10.74      inference('demod', [status(thm)], ['133', '134'])).
% 10.53/10.74  thf('136', plain,
% 10.53/10.74      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) = (sk_B))),
% 10.53/10.74      inference('demod', [status(thm)], ['116', '135'])).
% 10.53/10.74  thf('137', plain,
% 10.53/10.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.74  thf(t27_funct_2, axiom,
% 10.53/10.74    (![A:$i,B:$i,C:$i]:
% 10.53/10.74     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.53/10.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.53/10.74       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 10.53/10.74            ( ~( ( v2_funct_1 @ C ) <=>
% 10.53/10.74                 ( ![D:$i,E:$i]:
% 10.53/10.74                   ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ D @ A ) & 
% 10.53/10.74                       ( m1_subset_1 @
% 10.53/10.74                         E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) ) =>
% 10.53/10.74                     ( ![F:$i]:
% 10.53/10.74                       ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ A ) & 
% 10.53/10.74                           ( m1_subset_1 @
% 10.53/10.74                             F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) ) =>
% 10.53/10.74                         ( ( r2_relset_1 @
% 10.53/10.74                             D @ B @ ( k1_partfun1 @ D @ A @ A @ B @ E @ C ) @ 
% 10.53/10.74                             ( k1_partfun1 @ D @ A @ A @ B @ F @ C ) ) =>
% 10.53/10.74                           ( r2_relset_1 @ D @ A @ E @ F ) ) ) ) ) ) ) ) ) ) ))).
% 10.53/10.74  thf('138', plain,
% 10.53/10.74      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 10.53/10.74         (((X47) = (k1_xboole_0))
% 10.53/10.74          | ((X48) = (k1_xboole_0))
% 10.53/10.74          | ~ (v1_funct_1 @ X49)
% 10.53/10.74          | ~ (v1_funct_2 @ X49 @ X48 @ X47)
% 10.53/10.74          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47)))
% 10.53/10.74          | ~ (v1_funct_1 @ X50)
% 10.53/10.74          | ~ (v1_funct_2 @ X50 @ X51 @ X48)
% 10.53/10.74          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X48)))
% 10.53/10.74          | ~ (r2_relset_1 @ X51 @ X47 @ 
% 10.53/10.74               (k1_partfun1 @ X51 @ X48 @ X48 @ X47 @ X50 @ X49) @ 
% 10.53/10.74               (k1_partfun1 @ X51 @ X48 @ X48 @ X47 @ X52 @ X49))
% 10.53/10.74          | (r2_relset_1 @ X51 @ X48 @ X50 @ X52)
% 10.53/10.74          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X48)))
% 10.53/10.74          | ~ (v1_funct_2 @ X52 @ X51 @ X48)
% 10.53/10.74          | ~ (v1_funct_1 @ X52)
% 10.53/10.74          | ~ (v2_funct_1 @ X49))),
% 10.53/10.74      inference('cnf', [status(esa)], [t27_funct_2])).
% 10.53/10.74  thf('139', plain,
% 10.53/10.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.74         (~ (v2_funct_1 @ sk_B)
% 10.53/10.74          | ~ (v1_funct_1 @ X0)
% 10.53/10.74          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 10.53/10.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 10.53/10.74          | (r2_relset_1 @ X1 @ sk_A @ X2 @ X0)
% 10.53/10.74          | ~ (r2_relset_1 @ X1 @ sk_A @ 
% 10.53/10.74               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B) @ 
% 10.53/10.74               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 10.53/10.74          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 10.53/10.74          | ~ (v1_funct_2 @ X2 @ X1 @ sk_A)
% 10.53/10.74          | ~ (v1_funct_1 @ X2)
% 10.53/10.74          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 10.53/10.74          | ~ (v1_funct_1 @ sk_B)
% 10.53/10.74          | ((sk_A) = (k1_xboole_0))
% 10.53/10.74          | ((sk_A) = (k1_xboole_0)))),
% 10.53/10.74      inference('sup-', [status(thm)], ['137', '138'])).
% 10.53/10.74  thf('140', plain, ((v2_funct_1 @ sk_B)),
% 10.53/10.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.74  thf('141', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 10.53/10.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.74  thf('142', plain, ((v1_funct_1 @ sk_B)),
% 10.53/10.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.74  thf('143', plain,
% 10.53/10.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.74         (~ (v1_funct_1 @ X0)
% 10.53/10.74          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 10.53/10.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 10.53/10.74          | (r2_relset_1 @ X1 @ sk_A @ X2 @ X0)
% 10.53/10.74          | ~ (r2_relset_1 @ X1 @ sk_A @ 
% 10.53/10.74               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B) @ 
% 10.53/10.74               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 10.53/10.74          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 10.53/10.74          | ~ (v1_funct_2 @ X2 @ X1 @ sk_A)
% 10.53/10.74          | ~ (v1_funct_1 @ X2)
% 10.53/10.74          | ((sk_A) = (k1_xboole_0))
% 10.53/10.74          | ((sk_A) = (k1_xboole_0)))),
% 10.53/10.74      inference('demod', [status(thm)], ['139', '140', '141', '142'])).
% 10.53/10.74  thf('144', plain,
% 10.53/10.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.74         (((sk_A) = (k1_xboole_0))
% 10.53/10.74          | ~ (v1_funct_1 @ X2)
% 10.53/10.74          | ~ (v1_funct_2 @ X2 @ X1 @ sk_A)
% 10.53/10.74          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 10.53/10.74          | ~ (r2_relset_1 @ X1 @ sk_A @ 
% 10.53/10.74               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B) @ 
% 10.53/10.74               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 10.53/10.74          | (r2_relset_1 @ X1 @ sk_A @ X2 @ X0)
% 10.53/10.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 10.53/10.74          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 10.53/10.74          | ~ (v1_funct_1 @ X0))),
% 10.53/10.74      inference('simplify', [status(thm)], ['143'])).
% 10.53/10.74  thf('145', plain,
% 10.53/10.74      (![X0 : $i]:
% 10.53/10.74         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ 
% 10.53/10.74             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 10.53/10.74          | ~ (v1_funct_1 @ X0)
% 10.53/10.74          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 10.53/10.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 10.53/10.74          | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0)
% 10.53/10.74          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 10.53/10.74          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 10.53/10.74          | ~ (v1_funct_1 @ sk_C)
% 10.53/10.74          | ((sk_A) = (k1_xboole_0)))),
% 10.53/10.74      inference('sup-', [status(thm)], ['136', '144'])).
% 10.53/10.74  thf('146', plain,
% 10.53/10.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.74  thf('147', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 10.53/10.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.74  thf('148', plain, ((v1_funct_1 @ sk_C)),
% 10.53/10.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.74  thf('149', plain,
% 10.53/10.74      (![X0 : $i]:
% 10.53/10.74         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ 
% 10.53/10.74             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 10.53/10.74          | ~ (v1_funct_1 @ X0)
% 10.53/10.74          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 10.53/10.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 10.53/10.74          | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0)
% 10.53/10.74          | ((sk_A) = (k1_xboole_0)))),
% 10.53/10.74      inference('demod', [status(thm)], ['145', '146', '147', '148'])).
% 10.53/10.74  thf('150', plain,
% 10.53/10.74      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)
% 10.53/10.74        | ((sk_A) = (k1_xboole_0))
% 10.53/10.74        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))
% 10.53/10.74        | ~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 10.53/10.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 10.53/10.74        | ~ (v1_funct_2 @ (k6_relat_1 @ sk_A) @ sk_A @ sk_A)
% 10.53/10.74        | ~ (v1_funct_1 @ (k6_relat_1 @ sk_A)))),
% 10.53/10.74      inference('sup-', [status(thm)], ['107', '149'])).
% 10.53/10.74  thf('151', plain,
% 10.53/10.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.74  thf('152', plain,
% 10.53/10.74      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 10.53/10.74         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 10.53/10.74          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 10.53/10.74          | (r2_relset_1 @ X26 @ X27 @ X25 @ X28)
% 10.53/10.74          | ((X25) != (X28)))),
% 10.53/10.74      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 10.53/10.74  thf('153', plain,
% 10.53/10.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 10.53/10.74         ((r2_relset_1 @ X26 @ X27 @ X28 @ X28)
% 10.53/10.74          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 10.53/10.74      inference('simplify', [status(thm)], ['152'])).
% 10.53/10.74  thf('154', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 10.53/10.74      inference('sup-', [status(thm)], ['151', '153'])).
% 10.53/10.74  thf('155', plain,
% 10.53/10.74      (![X36 : $i]:
% 10.53/10.74         (m1_subset_1 @ (k6_relat_1 @ X36) @ 
% 10.53/10.74          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 10.53/10.74      inference('demod', [status(thm)], ['71', '72'])).
% 10.53/10.74  thf('156', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 10.53/10.74      inference('demod', [status(thm)], ['55', '56', '57', '58', '59', '68'])).
% 10.53/10.74  thf(t71_relat_1, axiom,
% 10.53/10.74    (![A:$i]:
% 10.53/10.74     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 10.53/10.74       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 10.53/10.74  thf('157', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 10.53/10.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.53/10.74  thf('158', plain,
% 10.53/10.74      (![X56 : $i]:
% 10.53/10.74         ((v1_funct_2 @ X56 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))
% 10.53/10.74          | ~ (v1_funct_1 @ X56)
% 10.53/10.74          | ~ (v1_relat_1 @ X56))),
% 10.53/10.74      inference('cnf', [status(esa)], [t3_funct_2])).
% 10.53/10.74  thf('159', plain,
% 10.53/10.74      (![X0 : $i]:
% 10.53/10.74         ((v1_funct_2 @ (k6_relat_1 @ X0) @ X0 @ 
% 10.53/10.74           (k2_relat_1 @ (k6_relat_1 @ X0)))
% 10.53/10.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 10.53/10.74          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 10.53/10.74      inference('sup+', [status(thm)], ['157', '158'])).
% 10.53/10.74  thf('160', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 10.53/10.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.53/10.74  thf(fc4_funct_1, axiom,
% 10.53/10.74    (![A:$i]:
% 10.53/10.74     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 10.53/10.74       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 10.53/10.74  thf('161', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 10.53/10.74      inference('cnf', [status(esa)], [fc4_funct_1])).
% 10.53/10.74  thf('162', plain,
% 10.53/10.74      (![X0 : $i]:
% 10.53/10.74         ((v1_funct_2 @ (k6_relat_1 @ X0) @ X0 @ X0)
% 10.53/10.74          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 10.53/10.74      inference('demod', [status(thm)], ['159', '160', '161'])).
% 10.53/10.74  thf('163', plain, ((v1_funct_2 @ (k6_relat_1 @ sk_A) @ sk_A @ sk_A)),
% 10.53/10.74      inference('sup-', [status(thm)], ['156', '162'])).
% 10.53/10.74  thf('164', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 10.53/10.74      inference('demod', [status(thm)], ['55', '56', '57', '58', '59', '68'])).
% 10.53/10.74  thf('165', plain,
% 10.53/10.74      ((((sk_A) = (k1_xboole_0))
% 10.53/10.74        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A)))),
% 10.53/10.74      inference('demod', [status(thm)], ['150', '154', '155', '163', '164'])).
% 10.53/10.74  thf('166', plain,
% 10.53/10.74      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))),
% 10.53/10.74      inference('demod', [status(thm)], ['0', '1'])).
% 10.53/10.74  thf('167', plain, (((sk_A) = (k1_xboole_0))),
% 10.53/10.74      inference('clc', [status(thm)], ['165', '166'])).
% 10.53/10.74  thf('168', plain, (((sk_A) = (k1_xboole_0))),
% 10.53/10.74      inference('clc', [status(thm)], ['165', '166'])).
% 10.53/10.74  thf('169', plain, (((sk_A) = (k1_xboole_0))),
% 10.53/10.74      inference('clc', [status(thm)], ['165', '166'])).
% 10.53/10.74  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 10.53/10.74  thf('170', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 10.53/10.74      inference('cnf', [status(esa)], [t81_relat_1])).
% 10.53/10.74  thf('171', plain,
% 10.53/10.74      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ k1_xboole_0)),
% 10.53/10.74      inference('demod', [status(thm)], ['2', '167', '168', '169', '170'])).
% 10.53/10.74  thf('172', plain,
% 10.53/10.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.74  thf('173', plain,
% 10.53/10.74      (![X57 : $i, X58 : $i]:
% 10.53/10.74         (((k1_relset_1 @ X57 @ X57 @ X58) = (X57))
% 10.53/10.74          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X57)))
% 10.53/10.74          | ~ (v1_funct_2 @ X58 @ X57 @ X57)
% 10.53/10.74          | ~ (v1_funct_1 @ X58))),
% 10.53/10.74      inference('cnf', [status(esa)], [t67_funct_2])).
% 10.53/10.74  thf('174', plain,
% 10.53/10.74      ((~ (v1_funct_1 @ sk_C)
% 10.53/10.74        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 10.53/10.74        | ((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A)))),
% 10.53/10.74      inference('sup-', [status(thm)], ['172', '173'])).
% 10.53/10.74  thf('175', plain, ((v1_funct_1 @ sk_C)),
% 10.53/10.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.74  thf('176', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 10.53/10.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.74  thf('177', plain,
% 10.53/10.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.74  thf('178', plain,
% 10.53/10.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 10.53/10.74         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 10.53/10.74          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 10.53/10.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 10.53/10.74  thf('179', plain,
% 10.53/10.74      (((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 10.53/10.74      inference('sup-', [status(thm)], ['177', '178'])).
% 10.53/10.74  thf('180', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 10.53/10.74      inference('demod', [status(thm)], ['174', '175', '176', '179'])).
% 10.53/10.74  thf(t64_relat_1, axiom,
% 10.53/10.74    (![A:$i]:
% 10.53/10.74     ( ( v1_relat_1 @ A ) =>
% 10.53/10.74       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 10.53/10.74           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 10.53/10.74         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 10.53/10.74  thf('181', plain,
% 10.53/10.74      (![X4 : $i]:
% 10.53/10.74         (((k1_relat_1 @ X4) != (k1_xboole_0))
% 10.53/10.74          | ((X4) = (k1_xboole_0))
% 10.53/10.74          | ~ (v1_relat_1 @ X4))),
% 10.53/10.74      inference('cnf', [status(esa)], [t64_relat_1])).
% 10.53/10.74  thf('182', plain,
% 10.53/10.74      ((((sk_A) != (k1_xboole_0))
% 10.53/10.74        | ~ (v1_relat_1 @ sk_C)
% 10.53/10.74        | ((sk_C) = (k1_xboole_0)))),
% 10.53/10.74      inference('sup-', [status(thm)], ['180', '181'])).
% 10.53/10.74  thf('183', plain,
% 10.53/10.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.53/10.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.74  thf('184', plain,
% 10.53/10.74      (![X10 : $i, X11 : $i, X12 : $i]:
% 10.53/10.74         ((v1_relat_1 @ X10)
% 10.53/10.74          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 10.53/10.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 10.53/10.74  thf('185', plain, ((v1_relat_1 @ sk_C)),
% 10.53/10.74      inference('sup-', [status(thm)], ['183', '184'])).
% 10.53/10.74  thf('186', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 10.53/10.74      inference('demod', [status(thm)], ['182', '185'])).
% 10.53/10.74  thf('187', plain, (((sk_A) = (k1_xboole_0))),
% 10.53/10.74      inference('clc', [status(thm)], ['165', '166'])).
% 10.53/10.74  thf('188', plain,
% 10.53/10.74      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 10.53/10.74      inference('demod', [status(thm)], ['186', '187'])).
% 10.53/10.74  thf('189', plain, (((sk_C) = (k1_xboole_0))),
% 10.53/10.74      inference('simplify', [status(thm)], ['188'])).
% 10.53/10.74  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 10.53/10.74  thf('190', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 10.53/10.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 10.53/10.74  thf(t3_subset, axiom,
% 10.53/10.74    (![A:$i,B:$i]:
% 10.53/10.74     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 10.53/10.74  thf('191', plain,
% 10.53/10.74      (![X1 : $i, X3 : $i]:
% 10.53/10.74         ((m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X3)) | ~ (r1_tarski @ X1 @ X3))),
% 10.53/10.74      inference('cnf', [status(esa)], [t3_subset])).
% 10.53/10.74  thf('192', plain,
% 10.53/10.74      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 10.53/10.74      inference('sup-', [status(thm)], ['190', '191'])).
% 10.53/10.74  thf('193', plain,
% 10.53/10.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 10.53/10.74         ((r2_relset_1 @ X26 @ X27 @ X28 @ X28)
% 10.53/10.74          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 10.53/10.74      inference('simplify', [status(thm)], ['152'])).
% 10.53/10.74  thf('194', plain,
% 10.53/10.74      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 10.53/10.74      inference('sup-', [status(thm)], ['192', '193'])).
% 10.53/10.74  thf('195', plain, ($false),
% 10.53/10.74      inference('demod', [status(thm)], ['171', '189', '194'])).
% 10.53/10.74  
% 10.53/10.74  % SZS output end Refutation
% 10.53/10.74  
% 10.53/10.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qb8iiGCt0M

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:22 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 131 expanded)
%              Number of leaves         :   29 (  51 expanded)
%              Depth                    :   18
%              Number of atoms          :  841 (1687 expanded)
%              Number of equality atoms :   13 (  14 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(a_3_0_waybel_9_type,type,(
    a_3_0_waybel_9: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_waybel_9_type,type,(
    k4_waybel_9: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t13_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
               => ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ ( u1_struct_0 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_waybel_9])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) )
        & ( v1_funct_2 @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( u1_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ~ ( l1_waybel_0 @ X10 @ X9 )
      | ( m1_subset_1 @ ( u1_waybel_0 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('3',plain,
    ( ( m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X8 ) ) )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( u1_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fraenkel_a_3_0_waybel_9,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( l1_struct_0 @ B )
        & ~ ( v2_struct_0 @ C )
        & ( l1_waybel_0 @ C @ B )
        & ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) )
     => ( ( r2_hidden @ A @ ( a_3_0_waybel_9 @ B @ C @ D ) )
      <=> ? [E: $i] :
            ( ( r1_orders_2 @ C @ D @ E )
            & ( A = E )
            & ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_waybel_0 @ X13 @ X14 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ( X16
        = ( sk_E @ X15 @ X13 @ X16 ) )
      | ~ ( r2_hidden @ X16 @ ( a_3_0_waybel_9 @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_3_0_waybel_9])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) )
      | ( X1
        = ( sk_E @ sk_C_1 @ sk_B @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X1 )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( sk_C @ X1 @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) )
        = ( sk_E @ sk_C_1 @ sk_B @ ( sk_C @ X1 @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
        = ( sk_E @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
        = ( sk_E @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_waybel_0 @ X13 @ X14 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ( m1_subset_1 @ ( sk_E @ X15 @ X13 @ X16 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_hidden @ X16 @ ( a_3_0_waybel_9 @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_3_0_waybel_9])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( a_3_0_waybel_9 @ X2 @ X1 @ X0 ) @ X3 )
      | ( m1_subset_1 @ ( sk_E @ X0 @ X1 @ ( sk_C @ X3 @ ( a_3_0_waybel_9 @ X2 @ X1 @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_waybel_0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_E @ sk_C_1 @ sk_B @ ( sk_C @ X1 @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_E @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_E @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_hidden @ ( sk_E @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,
    ( ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ~ ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) )
                = ( a_3_0_waybel_9 @ A @ B @ C ) ) ) ) ) )).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( ( u1_struct_0 @ ( k4_waybel_9 @ X19 @ X18 @ X20 ) )
        = ( a_3_0_waybel_9 @ X19 @ X18 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_waybel_9])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C_1 ) )
        = ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
    = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    v1_xboole_0 @ ( u1_waybel_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['7','50'])).

thf(fc15_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) )
        & ~ ( v1_xboole_0 @ ( u1_waybel_0 @ A @ B ) )
        & ( v1_funct_2 @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('52',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X11 )
      | ~ ( v1_xboole_0 @ ( u1_waybel_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fc15_yellow_6])).

thf('53',plain,
    ( ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['0','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qb8iiGCt0M
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:52:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 54 iterations in 0.032s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.19/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(a_3_0_waybel_9_type, type, a_3_0_waybel_9: $i > $i > $i > $i).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.19/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.48  thf(k4_waybel_9_type, type, k4_waybel_9: $i > $i > $i > $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.48  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.48  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.19/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.48  thf(t13_waybel_9, conjecture,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.48               ( r1_tarski @
% 0.19/0.48                 ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ 
% 0.19/0.48                 ( u1_struct_0 @ B ) ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i]:
% 0.19/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.48          ( ![B:$i]:
% 0.19/0.48            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.19/0.48              ( ![C:$i]:
% 0.19/0.48                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.48                  ( r1_tarski @
% 0.19/0.48                    ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ 
% 0.19/0.48                    ( u1_struct_0 @ B ) ) ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t13_waybel_9])).
% 0.19/0.48  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('1', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(dt_u1_waybel_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.19/0.48       ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) ) & 
% 0.19/0.48         ( v1_funct_2 @
% 0.19/0.48           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.48         ( m1_subset_1 @
% 0.19/0.48           ( u1_waybel_0 @ A @ B ) @ 
% 0.19/0.48           ( k1_zfmisc_1 @
% 0.19/0.48             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X9 : $i, X10 : $i]:
% 0.19/0.48         (~ (l1_struct_0 @ X9)
% 0.19/0.48          | ~ (l1_waybel_0 @ X10 @ X9)
% 0.19/0.48          | (m1_subset_1 @ (u1_waybel_0 @ X9 @ X10) @ 
% 0.19/0.48             (k1_zfmisc_1 @ 
% 0.19/0.48              (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9)))))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.19/0.48         (k1_zfmisc_1 @ 
% 0.19/0.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.19/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.48  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      ((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf(cc3_relset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( v1_xboole_0 @ A ) =>
% 0.19/0.48       ( ![C:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.48           ( v1_xboole_0 @ C ) ) ) ))).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.48         (~ (v1_xboole_0 @ X6)
% 0.19/0.48          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X8)))
% 0.19/0.48          | (v1_xboole_0 @ X7))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (((v1_xboole_0 @ (u1_waybel_0 @ sk_A @ sk_B))
% 0.19/0.48        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.48  thf('8', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(d3_tarski, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X1 : $i, X3 : $i]:
% 0.19/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.48  thf('10', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(fraenkel_a_3_0_waybel_9, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) & 
% 0.19/0.48         ( ~( v2_struct_0 @ C ) ) & ( l1_waybel_0 @ C @ B ) & 
% 0.19/0.48         ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) ) =>
% 0.19/0.48       ( ( r2_hidden @ A @ ( a_3_0_waybel_9 @ B @ C @ D ) ) <=>
% 0.19/0.48         ( ?[E:$i]:
% 0.19/0.48           ( ( r1_orders_2 @ C @ D @ E ) & ( ( A ) = ( E ) ) & 
% 0.19/0.48             ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ))).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.48         (~ (l1_waybel_0 @ X13 @ X14)
% 0.19/0.48          | (v2_struct_0 @ X13)
% 0.19/0.48          | ~ (l1_struct_0 @ X14)
% 0.19/0.48          | (v2_struct_0 @ X14)
% 0.19/0.48          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.19/0.48          | ((X16) = (sk_E @ X15 @ X13 @ X16))
% 0.19/0.48          | ~ (r2_hidden @ X16 @ (a_3_0_waybel_9 @ X14 @ X13 @ X15)))),
% 0.19/0.48      inference('cnf', [status(esa)], [fraenkel_a_3_0_waybel_9])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X1 @ (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1))
% 0.19/0.48          | ((X1) = (sk_E @ sk_C_1 @ sk_B @ X1))
% 0.19/0.48          | (v2_struct_0 @ X0)
% 0.19/0.48          | ~ (l1_struct_0 @ X0)
% 0.19/0.48          | (v2_struct_0 @ sk_B)
% 0.19/0.48          | ~ (l1_waybel_0 @ sk_B @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r1_tarski @ (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1) @ X1)
% 0.19/0.48          | ~ (l1_waybel_0 @ sk_B @ X0)
% 0.19/0.48          | (v2_struct_0 @ sk_B)
% 0.19/0.48          | ~ (l1_struct_0 @ X0)
% 0.19/0.48          | (v2_struct_0 @ X0)
% 0.19/0.48          | ((sk_C @ X1 @ (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1))
% 0.19/0.48              = (sk_E @ sk_C_1 @ sk_B @ 
% 0.19/0.48                 (sk_C @ X1 @ (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1)))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['9', '12'])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.19/0.48            = (sk_E @ sk_C_1 @ sk_B @ 
% 0.19/0.48               (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))))
% 0.19/0.48          | (v2_struct_0 @ sk_A)
% 0.19/0.48          | ~ (l1_struct_0 @ sk_A)
% 0.19/0.48          | (v2_struct_0 @ sk_B)
% 0.19/0.48          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['8', '13'])).
% 0.19/0.48  thf('15', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.19/0.48            = (sk_E @ sk_C_1 @ sk_B @ 
% 0.19/0.48               (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))))
% 0.19/0.48          | (v2_struct_0 @ sk_A)
% 0.19/0.48          | (v2_struct_0 @ sk_B)
% 0.19/0.48          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.19/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.19/0.48  thf('17', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('18', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X1 : $i, X3 : $i]:
% 0.19/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.48         (~ (l1_waybel_0 @ X13 @ X14)
% 0.19/0.48          | (v2_struct_0 @ X13)
% 0.19/0.48          | ~ (l1_struct_0 @ X14)
% 0.19/0.48          | (v2_struct_0 @ X14)
% 0.19/0.48          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.19/0.48          | (m1_subset_1 @ (sk_E @ X15 @ X13 @ X16) @ (u1_struct_0 @ X13))
% 0.19/0.48          | ~ (r2_hidden @ X16 @ (a_3_0_waybel_9 @ X14 @ X13 @ X15)))),
% 0.19/0.48      inference('cnf', [status(esa)], [fraenkel_a_3_0_waybel_9])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         ((r1_tarski @ (a_3_0_waybel_9 @ X2 @ X1 @ X0) @ X3)
% 0.19/0.48          | (m1_subset_1 @ 
% 0.19/0.48             (sk_E @ X0 @ X1 @ (sk_C @ X3 @ (a_3_0_waybel_9 @ X2 @ X1 @ X0))) @ 
% 0.19/0.48             (u1_struct_0 @ X1))
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.19/0.48          | (v2_struct_0 @ X2)
% 0.19/0.48          | ~ (l1_struct_0 @ X2)
% 0.19/0.48          | (v2_struct_0 @ X1)
% 0.19/0.48          | ~ (l1_waybel_0 @ X1 @ X2))),
% 0.19/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (l1_waybel_0 @ sk_B @ X0)
% 0.19/0.48          | (v2_struct_0 @ sk_B)
% 0.19/0.48          | ~ (l1_struct_0 @ X0)
% 0.19/0.48          | (v2_struct_0 @ X0)
% 0.19/0.48          | (m1_subset_1 @ 
% 0.19/0.48             (sk_E @ sk_C_1 @ sk_B @ 
% 0.19/0.48              (sk_C @ X1 @ (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1))) @ 
% 0.19/0.48             (u1_struct_0 @ sk_B))
% 0.19/0.48          | (r1_tarski @ (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1) @ X1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['18', '21'])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.19/0.48          | (m1_subset_1 @ 
% 0.19/0.48             (sk_E @ sk_C_1 @ sk_B @ 
% 0.19/0.48              (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.19/0.48             (u1_struct_0 @ sk_B))
% 0.19/0.48          | (v2_struct_0 @ sk_A)
% 0.19/0.48          | ~ (l1_struct_0 @ sk_A)
% 0.19/0.48          | (v2_struct_0 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['17', '22'])).
% 0.19/0.48  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.19/0.48          | (m1_subset_1 @ 
% 0.19/0.48             (sk_E @ sk_C_1 @ sk_B @ 
% 0.19/0.48              (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.19/0.48             (u1_struct_0 @ sk_B))
% 0.19/0.48          | (v2_struct_0 @ sk_A)
% 0.19/0.48          | (v2_struct_0 @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['23', '24'])).
% 0.19/0.48  thf(t2_subset, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ A @ B ) =>
% 0.19/0.48       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i]:
% 0.19/0.48         ((r2_hidden @ X4 @ X5)
% 0.19/0.48          | (v1_xboole_0 @ X5)
% 0.19/0.48          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.19/0.48      inference('cnf', [status(esa)], [t2_subset])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v2_struct_0 @ sk_B)
% 0.19/0.48          | (v2_struct_0 @ sk_A)
% 0.19/0.48          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.19/0.48          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.48          | (r2_hidden @ 
% 0.19/0.48             (sk_E @ sk_C_1 @ sk_B @ 
% 0.19/0.48              (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.19/0.48             (u1_struct_0 @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r2_hidden @ (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.19/0.48           (u1_struct_0 @ sk_B))
% 0.19/0.48          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.19/0.48          | (v2_struct_0 @ sk_B)
% 0.19/0.48          | (v2_struct_0 @ sk_A)
% 0.19/0.48          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.48          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.19/0.48          | (v2_struct_0 @ sk_A)
% 0.19/0.48          | (v2_struct_0 @ sk_B))),
% 0.19/0.48      inference('sup+', [status(thm)], ['16', '27'])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.48          | (v2_struct_0 @ sk_A)
% 0.19/0.48          | (v2_struct_0 @ sk_B)
% 0.19/0.48          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.19/0.48          | (r2_hidden @ 
% 0.19/0.48             (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.19/0.48             (u1_struct_0 @ sk_B)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['28'])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      (![X1 : $i, X3 : $i]:
% 0.19/0.48         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.48  thf('31', plain,
% 0.19/0.48      (((r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.19/0.48         (u1_struct_0 @ sk_B))
% 0.19/0.48        | (v2_struct_0 @ sk_B)
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.48        | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.19/0.48           (u1_struct_0 @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | (v2_struct_0 @ sk_B)
% 0.19/0.48        | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.19/0.48           (u1_struct_0 @ sk_B)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['31'])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      (~ (r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.19/0.48          (u1_struct_0 @ sk_B))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('34', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('35', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t12_waybel_9, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.48               ( ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) =
% 0.19/0.48                 ( a_3_0_waybel_9 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.48         ((v2_struct_0 @ X18)
% 0.19/0.48          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.19/0.48          | ((u1_struct_0 @ (k4_waybel_9 @ X19 @ X18 @ X20))
% 0.19/0.48              = (a_3_0_waybel_9 @ X19 @ X18 @ X20))
% 0.19/0.48          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.19/0.48          | ~ (l1_struct_0 @ X19)
% 0.19/0.48          | (v2_struct_0 @ X19))),
% 0.19/0.48      inference('cnf', [status(esa)], [t12_waybel_9])).
% 0.19/0.48  thf('37', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v2_struct_0 @ X0)
% 0.19/0.48          | ~ (l1_struct_0 @ X0)
% 0.19/0.48          | ((u1_struct_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C_1))
% 0.19/0.48              = (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1))
% 0.19/0.48          | ~ (l1_waybel_0 @ sk_B @ X0)
% 0.19/0.48          | (v2_struct_0 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.48  thf('38', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_B)
% 0.19/0.48        | ((u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.19/0.48            = (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.19/0.48        | ~ (l1_struct_0 @ sk_A)
% 0.19/0.48        | (v2_struct_0 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['34', '37'])).
% 0.19/0.48  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('40', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_B)
% 0.19/0.48        | ((u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.19/0.48            = (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.19/0.48        | (v2_struct_0 @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['38', '39'])).
% 0.19/0.48  thf('41', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('42', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | ((u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.19/0.48            = (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)))),
% 0.19/0.48      inference('clc', [status(thm)], ['40', '41'])).
% 0.19/0.48  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('44', plain,
% 0.19/0.48      (((u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.19/0.48         = (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))),
% 0.19/0.48      inference('clc', [status(thm)], ['42', '43'])).
% 0.19/0.48  thf('45', plain,
% 0.19/0.48      (~ (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.19/0.48          (u1_struct_0 @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['33', '44'])).
% 0.19/0.48  thf('46', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_B)
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['32', '45'])).
% 0.19/0.48  thf('47', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('48', plain,
% 0.19/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.19/0.48      inference('clc', [status(thm)], ['46', '47'])).
% 0.19/0.48  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('50', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.19/0.48      inference('clc', [status(thm)], ['48', '49'])).
% 0.19/0.48  thf('51', plain, ((v1_xboole_0 @ (u1_waybel_0 @ sk_A @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['7', '50'])).
% 0.19/0.48  thf(fc15_yellow_6, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.19/0.48         ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.19/0.48       ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) ) & 
% 0.19/0.48         ( ~( v1_xboole_0 @ ( u1_waybel_0 @ A @ B ) ) ) & 
% 0.19/0.48         ( v1_funct_2 @
% 0.19/0.48           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.48  thf('52', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i]:
% 0.19/0.48         (~ (l1_struct_0 @ X11)
% 0.19/0.48          | (v2_struct_0 @ X11)
% 0.19/0.48          | (v2_struct_0 @ X12)
% 0.19/0.48          | ~ (l1_waybel_0 @ X12 @ X11)
% 0.19/0.48          | ~ (v1_xboole_0 @ (u1_waybel_0 @ X11 @ X12)))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc15_yellow_6])).
% 0.19/0.48  thf('53', plain,
% 0.19/0.48      ((~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.19/0.48        | (v2_struct_0 @ sk_B)
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['51', '52'])).
% 0.19/0.48  thf('54', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('55', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('56', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.19/0.48  thf('57', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('58', plain, ((v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('clc', [status(thm)], ['56', '57'])).
% 0.19/0.48  thf('59', plain, ($false), inference('demod', [status(thm)], ['0', '58'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

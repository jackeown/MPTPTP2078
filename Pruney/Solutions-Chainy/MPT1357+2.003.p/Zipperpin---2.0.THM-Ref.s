%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DK2GdnfpxV

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:34 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 652 expanded)
%              Number of leaves         :   29 ( 195 expanded)
%              Depth                    :   17
%              Number of atoms          :  866 (9120 expanded)
%              Number of equality atoms :   29 ( 498 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(t12_compts_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( B = k1_xboole_0 )
             => ( ( v2_compts_1 @ B @ A )
              <=> ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) )
            & ( ( v2_pre_topc @ A )
             => ( ( B = k1_xboole_0 )
                | ( ( v2_compts_1 @ B @ A )
                <=> ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( B = k1_xboole_0 )
               => ( ( v2_compts_1 @ B @ A )
                <=> ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) )
              & ( ( v2_pre_topc @ A )
               => ( ( B = k1_xboole_0 )
                  | ( ( v2_compts_1 @ B @ A )
                  <=> ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_compts_1])).

thf('0',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
   <= ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X12 @ X11 ) )
        = X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
    | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t11_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ C @ ( k2_struct_0 @ B ) )
               => ( ( v2_compts_1 @ C @ A )
                <=> ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( D = C )
                       => ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( r1_tarski @ X19 @ ( k2_struct_0 @ X17 ) )
      | ~ ( v2_compts_1 @ X19 @ X18 )
      | ( X20 != X19 )
      | ( v2_compts_1 @ X20 @ X17 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('12',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v2_compts_1 @ X19 @ X17 )
      | ~ ( v2_compts_1 @ X19 @ X18 )
      | ~ ( r1_tarski @ X19 @ ( k2_struct_0 @ X17 ) )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
      | ~ ( v2_compts_1 @ sk_B @ sk_A )
      | ( v2_compts_1 @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
      | ~ ( v2_compts_1 @ sk_B @ sk_A )
      | ( v2_compts_1 @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v2_compts_1 @ sk_B @ X0 )
        | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A ) )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
      | ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('18',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('19',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('20',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X6 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('23',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['5','6'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('27',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('28',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['23','24'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( l1_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('34',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('35',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['28','35'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['17','20','25','36','38'])).

thf('40',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['28','35'])).

thf(t10_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_compts_1 @ A )
      <=> ( v2_compts_1 @ ( k2_struct_0 @ A ) @ A ) ) ) )).

thf('41',plain,(
    ! [X16: $i] :
      ( ~ ( v2_compts_1 @ ( k2_struct_0 @ X16 ) @ X16 )
      | ( v1_compts_1 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t10_compts_1])).

thf('42',plain,
    ( ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('44',plain,
    ( ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,
    ( ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,
    ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','47'])).

thf('49',plain,(
    ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','48'])).

thf('50',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['28','35'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( r1_tarski @ X19 @ ( k2_struct_0 @ X17 ) )
      | ~ ( v2_compts_1 @ ( sk_D @ X19 @ X17 ) @ X17 )
      | ( v2_compts_1 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_B @ sk_A )
      | ~ ( v2_compts_1 @ ( sk_D @ sk_B @ X0 ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_B @ sk_A )
      | ~ ( v2_compts_1 @ ( sk_D @ sk_B @ X0 ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_compts_1 @ ( sk_D @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('58',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['23','24'])).

thf('59',plain,
    ( ~ ( v2_compts_1 @ ( sk_D @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['28','35'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( r1_tarski @ X19 @ ( k2_struct_0 @ X17 ) )
      | ( ( sk_D @ X19 @ X17 )
        = X19 )
      | ( v2_compts_1 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_B @ sk_A )
      | ( ( sk_D @ sk_B @ X0 )
        = sk_B )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_B @ sk_A )
      | ( ( sk_D @ sk_B @ X0 )
        = sk_B )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_D @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('68',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['23','24'])).

thf('69',plain,
    ( ( ( sk_D @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','48'])).

thf('71',plain,
    ( ( sk_D @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('73',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['28','35'])).

thf('74',plain,(
    ! [X16: $i] :
      ( ~ ( v1_compts_1 @ X16 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t10_compts_1])).

thf('75',plain,
    ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('77',plain,
    ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,
    ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('80',plain,(
    v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','47','79'])).

thf('81',plain,(
    v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['78','80'])).

thf('82',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['59','71','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['49','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DK2GdnfpxV
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.72/1.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.72/1.92  % Solved by: fo/fo7.sh
% 1.72/1.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.72/1.92  % done 1603 iterations in 1.470s
% 1.72/1.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.72/1.92  % SZS output start Refutation
% 1.72/1.92  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.72/1.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.72/1.92  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.72/1.92  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.72/1.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.72/1.92  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.72/1.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.72/1.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.72/1.92  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.72/1.92  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 1.72/1.92  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.72/1.92  thf(sk_B_type, type, sk_B: $i).
% 1.72/1.92  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.72/1.92  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 1.72/1.92  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.72/1.92  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 1.72/1.92  thf(sk_A_type, type, sk_A: $i).
% 1.72/1.92  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.72/1.92  thf(t12_compts_1, conjecture,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( l1_pre_topc @ A ) =>
% 1.72/1.92       ( ![B:$i]:
% 1.72/1.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.92           ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.72/1.92               ( ( v2_compts_1 @ B @ A ) <=>
% 1.72/1.92                 ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) & 
% 1.72/1.92             ( ( v2_pre_topc @ A ) =>
% 1.72/1.92               ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.72/1.92                 ( ( v2_compts_1 @ B @ A ) <=>
% 1.72/1.92                   ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) ))).
% 1.72/1.92  thf(zf_stmt_0, negated_conjecture,
% 1.72/1.92    (~( ![A:$i]:
% 1.72/1.92        ( ( l1_pre_topc @ A ) =>
% 1.72/1.92          ( ![B:$i]:
% 1.72/1.92            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.92              ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.72/1.92                  ( ( v2_compts_1 @ B @ A ) <=>
% 1.72/1.92                    ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) & 
% 1.72/1.92                ( ( v2_pre_topc @ A ) =>
% 1.72/1.92                  ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.72/1.92                    ( ( v2_compts_1 @ B @ A ) <=>
% 1.72/1.92                      ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) ) )),
% 1.72/1.92    inference('cnf.neg', [status(esa)], [t12_compts_1])).
% 1.72/1.92  thf('0', plain,
% 1.72/1.92      ((~ (v2_compts_1 @ sk_B @ sk_A)
% 1.72/1.92        | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.72/1.92        | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.72/1.92        | ~ (v2_compts_1 @ sk_B @ sk_A))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('1', plain,
% 1.72/1.92      ((~ (v2_compts_1 @ sk_B @ sk_A)) <= (~ ((v2_compts_1 @ sk_B @ sk_A)))),
% 1.72/1.92      inference('split', [status(esa)], ['0'])).
% 1.72/1.92  thf('2', plain,
% 1.72/1.92      (~ ((v2_compts_1 @ sk_B @ sk_A)) | 
% 1.72/1.92       ~ ((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 1.72/1.92      inference('split', [status(esa)], ['0'])).
% 1.72/1.92  thf('3', plain,
% 1.72/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf(t29_pre_topc, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( l1_pre_topc @ A ) =>
% 1.72/1.92       ( ![B:$i]:
% 1.72/1.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.92           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 1.72/1.92  thf('4', plain,
% 1.72/1.92      (![X11 : $i, X12 : $i]:
% 1.72/1.92         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.72/1.92          | ((u1_struct_0 @ (k1_pre_topc @ X12 @ X11)) = (X11))
% 1.72/1.92          | ~ (l1_pre_topc @ X12))),
% 1.72/1.92      inference('cnf', [status(esa)], [t29_pre_topc])).
% 1.72/1.92  thf('5', plain,
% 1.72/1.92      ((~ (l1_pre_topc @ sk_A)
% 1.72/1.92        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['3', '4'])).
% 1.72/1.92  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('7', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 1.72/1.92      inference('demod', [status(thm)], ['5', '6'])).
% 1.72/1.92  thf('8', plain,
% 1.72/1.92      (((v2_compts_1 @ sk_B @ sk_A)
% 1.72/1.92        | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.72/1.92        | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.72/1.92        | (v2_compts_1 @ sk_B @ sk_A))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('9', plain,
% 1.72/1.92      (((v2_compts_1 @ sk_B @ sk_A)) <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 1.72/1.92      inference('split', [status(esa)], ['8'])).
% 1.72/1.92  thf('10', plain,
% 1.72/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf(t11_compts_1, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( l1_pre_topc @ A ) =>
% 1.72/1.92       ( ![B:$i]:
% 1.72/1.92         ( ( m1_pre_topc @ B @ A ) =>
% 1.72/1.92           ( ![C:$i]:
% 1.72/1.92             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.92               ( ( r1_tarski @ C @ ( k2_struct_0 @ B ) ) =>
% 1.72/1.92                 ( ( v2_compts_1 @ C @ A ) <=>
% 1.72/1.92                   ( ![D:$i]:
% 1.72/1.92                     ( ( m1_subset_1 @
% 1.72/1.92                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.72/1.92                       ( ( ( D ) = ( C ) ) => ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 1.72/1.92  thf('11', plain,
% 1.72/1.92      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.72/1.92         (~ (m1_pre_topc @ X17 @ X18)
% 1.72/1.92          | ~ (r1_tarski @ X19 @ (k2_struct_0 @ X17))
% 1.72/1.92          | ~ (v2_compts_1 @ X19 @ X18)
% 1.72/1.92          | ((X20) != (X19))
% 1.72/1.92          | (v2_compts_1 @ X20 @ X17)
% 1.72/1.92          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.72/1.92          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.72/1.92          | ~ (l1_pre_topc @ X18))),
% 1.72/1.92      inference('cnf', [status(esa)], [t11_compts_1])).
% 1.72/1.92  thf('12', plain,
% 1.72/1.92      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.72/1.92         (~ (l1_pre_topc @ X18)
% 1.72/1.92          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.72/1.92          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.72/1.92          | (v2_compts_1 @ X19 @ X17)
% 1.72/1.92          | ~ (v2_compts_1 @ X19 @ X18)
% 1.72/1.92          | ~ (r1_tarski @ X19 @ (k2_struct_0 @ X17))
% 1.72/1.92          | ~ (m1_pre_topc @ X17 @ X18))),
% 1.72/1.92      inference('simplify', [status(thm)], ['11'])).
% 1.72/1.92  thf('13', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.72/1.92          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 1.72/1.92          | ~ (v2_compts_1 @ sk_B @ sk_A)
% 1.72/1.92          | (v2_compts_1 @ sk_B @ X0)
% 1.72/1.92          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.72/1.92          | ~ (l1_pre_topc @ sk_A))),
% 1.72/1.92      inference('sup-', [status(thm)], ['10', '12'])).
% 1.72/1.92  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('15', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.72/1.92          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 1.72/1.92          | ~ (v2_compts_1 @ sk_B @ sk_A)
% 1.72/1.92          | (v2_compts_1 @ sk_B @ X0)
% 1.72/1.92          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.72/1.92      inference('demod', [status(thm)], ['13', '14'])).
% 1.72/1.92  thf('16', plain,
% 1.72/1.92      ((![X0 : $i]:
% 1.72/1.92          (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.72/1.92           | (v2_compts_1 @ sk_B @ X0)
% 1.72/1.92           | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 1.72/1.92           | ~ (m1_pre_topc @ X0 @ sk_A)))
% 1.72/1.92         <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['9', '15'])).
% 1.72/1.92  thf('17', plain,
% 1.72/1.92      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B))
% 1.72/1.92         | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.72/1.92         | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))
% 1.72/1.92         | (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))))
% 1.72/1.92         <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['7', '16'])).
% 1.72/1.92  thf(dt_k2_subset_1, axiom,
% 1.72/1.92    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.72/1.92  thf('18', plain,
% 1.72/1.92      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.72/1.92  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.72/1.92  thf('19', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 1.72/1.92      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.72/1.92  thf('20', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 1.72/1.92      inference('demod', [status(thm)], ['18', '19'])).
% 1.72/1.92  thf('21', plain,
% 1.72/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf(dt_k1_pre_topc, axiom,
% 1.72/1.92    (![A:$i,B:$i]:
% 1.72/1.92     ( ( ( l1_pre_topc @ A ) & 
% 1.72/1.92         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.72/1.92       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 1.72/1.92         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 1.72/1.92  thf('22', plain,
% 1.72/1.92      (![X6 : $i, X7 : $i]:
% 1.72/1.92         (~ (l1_pre_topc @ X6)
% 1.72/1.92          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 1.72/1.92          | (m1_pre_topc @ (k1_pre_topc @ X6 @ X7) @ X6))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 1.72/1.92  thf('23', plain,
% 1.72/1.92      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.72/1.92        | ~ (l1_pre_topc @ sk_A))),
% 1.72/1.92      inference('sup-', [status(thm)], ['21', '22'])).
% 1.72/1.92  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('25', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.72/1.92      inference('demod', [status(thm)], ['23', '24'])).
% 1.72/1.92  thf('26', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 1.72/1.92      inference('demod', [status(thm)], ['5', '6'])).
% 1.72/1.92  thf(d3_struct_0, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.72/1.92  thf('27', plain,
% 1.72/1.92      (![X5 : $i]:
% 1.72/1.92         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 1.72/1.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.72/1.92  thf('28', plain,
% 1.72/1.92      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 1.72/1.92        | ~ (l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 1.72/1.92      inference('sup+', [status(thm)], ['26', '27'])).
% 1.72/1.92  thf('29', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.72/1.92      inference('demod', [status(thm)], ['23', '24'])).
% 1.72/1.92  thf(dt_m1_pre_topc, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( l1_pre_topc @ A ) =>
% 1.72/1.92       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.72/1.92  thf('30', plain,
% 1.72/1.92      (![X9 : $i, X10 : $i]:
% 1.72/1.92         (~ (m1_pre_topc @ X9 @ X10)
% 1.72/1.92          | (l1_pre_topc @ X9)
% 1.72/1.92          | ~ (l1_pre_topc @ X10))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.72/1.92  thf('31', plain,
% 1.72/1.92      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['29', '30'])).
% 1.72/1.92  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('33', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 1.72/1.92      inference('demod', [status(thm)], ['31', '32'])).
% 1.72/1.92  thf(dt_l1_pre_topc, axiom,
% 1.72/1.92    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.72/1.92  thf('34', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 1.72/1.92      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.72/1.92  thf('35', plain, ((l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 1.72/1.92      inference('sup-', [status(thm)], ['33', '34'])).
% 1.72/1.92  thf('36', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 1.72/1.92      inference('demod', [status(thm)], ['28', '35'])).
% 1.72/1.92  thf(d10_xboole_0, axiom,
% 1.72/1.92    (![A:$i,B:$i]:
% 1.72/1.92     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.72/1.92  thf('37', plain,
% 1.72/1.92      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.72/1.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.72/1.92  thf('38', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.72/1.92      inference('simplify', [status(thm)], ['37'])).
% 1.72/1.92  thf('39', plain,
% 1.72/1.92      (((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)))
% 1.72/1.92         <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 1.72/1.92      inference('demod', [status(thm)], ['17', '20', '25', '36', '38'])).
% 1.72/1.92  thf('40', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 1.72/1.92      inference('demod', [status(thm)], ['28', '35'])).
% 1.72/1.92  thf(t10_compts_1, axiom,
% 1.72/1.92    (![A:$i]:
% 1.72/1.92     ( ( l1_pre_topc @ A ) =>
% 1.72/1.92       ( ( v1_compts_1 @ A ) <=> ( v2_compts_1 @ ( k2_struct_0 @ A ) @ A ) ) ))).
% 1.72/1.92  thf('41', plain,
% 1.72/1.92      (![X16 : $i]:
% 1.72/1.92         (~ (v2_compts_1 @ (k2_struct_0 @ X16) @ X16)
% 1.72/1.92          | (v1_compts_1 @ X16)
% 1.72/1.92          | ~ (l1_pre_topc @ X16))),
% 1.72/1.92      inference('cnf', [status(esa)], [t10_compts_1])).
% 1.72/1.92  thf('42', plain,
% 1.72/1.92      ((~ (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))
% 1.72/1.92        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 1.72/1.92        | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['40', '41'])).
% 1.72/1.92  thf('43', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 1.72/1.92      inference('demod', [status(thm)], ['31', '32'])).
% 1.72/1.92  thf('44', plain,
% 1.72/1.92      ((~ (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))
% 1.72/1.92        | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 1.72/1.92      inference('demod', [status(thm)], ['42', '43'])).
% 1.72/1.92  thf('45', plain,
% 1.72/1.92      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))
% 1.72/1.92         <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 1.72/1.92      inference('sup-', [status(thm)], ['39', '44'])).
% 1.72/1.92  thf('46', plain,
% 1.72/1.92      ((~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))
% 1.72/1.92         <= (~ ((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 1.72/1.92      inference('split', [status(esa)], ['0'])).
% 1.72/1.92  thf('47', plain,
% 1.72/1.92      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))) | 
% 1.72/1.92       ~ ((v2_compts_1 @ sk_B @ sk_A))),
% 1.72/1.92      inference('sup-', [status(thm)], ['45', '46'])).
% 1.72/1.92  thf('48', plain, (~ ((v2_compts_1 @ sk_B @ sk_A))),
% 1.72/1.92      inference('sat_resolution*', [status(thm)], ['2', '47'])).
% 1.72/1.92  thf('49', plain, (~ (v2_compts_1 @ sk_B @ sk_A)),
% 1.72/1.92      inference('simpl_trail', [status(thm)], ['1', '48'])).
% 1.72/1.92  thf('50', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 1.72/1.92      inference('demod', [status(thm)], ['28', '35'])).
% 1.72/1.92  thf('51', plain,
% 1.72/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('52', plain,
% 1.72/1.92      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.72/1.92         (~ (m1_pre_topc @ X17 @ X18)
% 1.72/1.92          | ~ (r1_tarski @ X19 @ (k2_struct_0 @ X17))
% 1.72/1.92          | ~ (v2_compts_1 @ (sk_D @ X19 @ X17) @ X17)
% 1.72/1.92          | (v2_compts_1 @ X19 @ X18)
% 1.72/1.92          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.72/1.92          | ~ (l1_pre_topc @ X18))),
% 1.72/1.92      inference('cnf', [status(esa)], [t11_compts_1])).
% 1.72/1.92  thf('53', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (l1_pre_topc @ sk_A)
% 1.72/1.92          | (v2_compts_1 @ sk_B @ sk_A)
% 1.72/1.92          | ~ (v2_compts_1 @ (sk_D @ sk_B @ X0) @ X0)
% 1.72/1.92          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 1.72/1.92          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.72/1.92      inference('sup-', [status(thm)], ['51', '52'])).
% 1.72/1.92  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('55', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         ((v2_compts_1 @ sk_B @ sk_A)
% 1.72/1.92          | ~ (v2_compts_1 @ (sk_D @ sk_B @ X0) @ X0)
% 1.72/1.92          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 1.72/1.92          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.72/1.92      inference('demod', [status(thm)], ['53', '54'])).
% 1.72/1.92  thf('56', plain,
% 1.72/1.92      ((~ (r1_tarski @ sk_B @ sk_B)
% 1.72/1.92        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.72/1.92        | ~ (v2_compts_1 @ (sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 1.72/1.92             (k1_pre_topc @ sk_A @ sk_B))
% 1.72/1.92        | (v2_compts_1 @ sk_B @ sk_A))),
% 1.72/1.92      inference('sup-', [status(thm)], ['50', '55'])).
% 1.72/1.92  thf('57', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.72/1.92      inference('simplify', [status(thm)], ['37'])).
% 1.72/1.92  thf('58', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.72/1.92      inference('demod', [status(thm)], ['23', '24'])).
% 1.72/1.92  thf('59', plain,
% 1.72/1.92      ((~ (v2_compts_1 @ (sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 1.72/1.92           (k1_pre_topc @ sk_A @ sk_B))
% 1.72/1.92        | (v2_compts_1 @ sk_B @ sk_A))),
% 1.72/1.92      inference('demod', [status(thm)], ['56', '57', '58'])).
% 1.72/1.92  thf('60', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 1.72/1.92      inference('demod', [status(thm)], ['28', '35'])).
% 1.72/1.92  thf('61', plain,
% 1.72/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('62', plain,
% 1.72/1.92      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.72/1.92         (~ (m1_pre_topc @ X17 @ X18)
% 1.72/1.92          | ~ (r1_tarski @ X19 @ (k2_struct_0 @ X17))
% 1.72/1.92          | ((sk_D @ X19 @ X17) = (X19))
% 1.72/1.92          | (v2_compts_1 @ X19 @ X18)
% 1.72/1.92          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.72/1.92          | ~ (l1_pre_topc @ X18))),
% 1.72/1.92      inference('cnf', [status(esa)], [t11_compts_1])).
% 1.72/1.92  thf('63', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         (~ (l1_pre_topc @ sk_A)
% 1.72/1.92          | (v2_compts_1 @ sk_B @ sk_A)
% 1.72/1.92          | ((sk_D @ sk_B @ X0) = (sk_B))
% 1.72/1.92          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 1.72/1.92          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.72/1.92      inference('sup-', [status(thm)], ['61', '62'])).
% 1.72/1.92  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.92  thf('65', plain,
% 1.72/1.92      (![X0 : $i]:
% 1.72/1.92         ((v2_compts_1 @ sk_B @ sk_A)
% 1.72/1.92          | ((sk_D @ sk_B @ X0) = (sk_B))
% 1.72/1.92          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 1.72/1.92          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.72/1.92      inference('demod', [status(thm)], ['63', '64'])).
% 1.72/1.92  thf('66', plain,
% 1.72/1.92      ((~ (r1_tarski @ sk_B @ sk_B)
% 1.72/1.92        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.72/1.92        | ((sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 1.72/1.92        | (v2_compts_1 @ sk_B @ sk_A))),
% 1.72/1.92      inference('sup-', [status(thm)], ['60', '65'])).
% 1.72/1.92  thf('67', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.72/1.92      inference('simplify', [status(thm)], ['37'])).
% 1.72/1.92  thf('68', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.72/1.92      inference('demod', [status(thm)], ['23', '24'])).
% 1.72/1.92  thf('69', plain,
% 1.72/1.92      ((((sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 1.72/1.92        | (v2_compts_1 @ sk_B @ sk_A))),
% 1.72/1.92      inference('demod', [status(thm)], ['66', '67', '68'])).
% 1.72/1.92  thf('70', plain, (~ (v2_compts_1 @ sk_B @ sk_A)),
% 1.72/1.92      inference('simpl_trail', [status(thm)], ['1', '48'])).
% 1.72/1.92  thf('71', plain, (((sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 1.72/1.92      inference('clc', [status(thm)], ['69', '70'])).
% 1.72/1.92  thf('72', plain,
% 1.72/1.92      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))
% 1.72/1.92         <= (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 1.72/1.92      inference('split', [status(esa)], ['8'])).
% 1.72/1.92  thf('73', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 1.72/1.92      inference('demod', [status(thm)], ['28', '35'])).
% 1.72/1.92  thf('74', plain,
% 1.72/1.92      (![X16 : $i]:
% 1.72/1.92         (~ (v1_compts_1 @ X16)
% 1.72/1.92          | (v2_compts_1 @ (k2_struct_0 @ X16) @ X16)
% 1.72/1.92          | ~ (l1_pre_topc @ X16))),
% 1.72/1.92      inference('cnf', [status(esa)], [t10_compts_1])).
% 1.72/1.92  thf('75', plain,
% 1.72/1.92      (((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))
% 1.72/1.92        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 1.72/1.92        | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 1.72/1.92      inference('sup+', [status(thm)], ['73', '74'])).
% 1.72/1.92  thf('76', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 1.72/1.92      inference('demod', [status(thm)], ['31', '32'])).
% 1.72/1.92  thf('77', plain,
% 1.72/1.92      (((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))
% 1.72/1.92        | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 1.72/1.92      inference('demod', [status(thm)], ['75', '76'])).
% 1.72/1.92  thf('78', plain,
% 1.72/1.92      (((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)))
% 1.72/1.92         <= (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 1.72/1.92      inference('sup-', [status(thm)], ['72', '77'])).
% 1.72/1.92  thf('79', plain,
% 1.72/1.92      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))) | 
% 1.72/1.92       ((v2_compts_1 @ sk_B @ sk_A))),
% 1.72/1.92      inference('split', [status(esa)], ['8'])).
% 1.72/1.92  thf('80', plain, (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 1.72/1.92      inference('sat_resolution*', [status(thm)], ['2', '47', '79'])).
% 1.72/1.92  thf('81', plain, ((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))),
% 1.72/1.92      inference('simpl_trail', [status(thm)], ['78', '80'])).
% 1.72/1.92  thf('82', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 1.72/1.92      inference('demod', [status(thm)], ['59', '71', '81'])).
% 1.72/1.92  thf('83', plain, ($false), inference('demod', [status(thm)], ['49', '82'])).
% 1.72/1.92  
% 1.72/1.92  % SZS output end Refutation
% 1.72/1.92  
% 1.72/1.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1670+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FbXJ4MGYoN

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:58 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 549 expanded)
%              Number of leaves         :   39 ( 173 expanded)
%              Depth                    :   26
%              Number of atoms          : 1774 (6997 expanded)
%              Number of equality atoms :   37 (  75 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(k12_waybel_0_type,type,(
    k12_waybel_0: $i > $i > $i )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k11_waybel_0_type,type,(
    k11_waybel_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(a_2_3_waybel_0_type,type,(
    a_2_3_waybel_0: $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(a_2_2_waybel_0_type,type,(
    a_2_2_waybel_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t50_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r1_tarski @ B @ ( k11_waybel_0 @ A @ B ) )
            & ( r1_tarski @ B @ ( k12_waybel_0 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( r1_tarski @ B @ ( k11_waybel_0 @ A @ B ) )
              & ( r1_tarski @ B @ ( k12_waybel_0 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_waybel_0])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k11_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ ( k12_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k12_waybel_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k12_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k11_waybel_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k11_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('6',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( m1_subset_1 @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) )
        = ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t39_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( ( k1_yellow_0 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
              = B )
            & ( ( k2_yellow_0 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
              = B ) ) ) ) )).

thf('12',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( ( k1_yellow_0 @ X29 @ ( k6_domain_1 @ ( u1_struct_0 @ X29 ) @ X28 ) )
        = X28 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) )
        = ( sk_C @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) )
        = ( sk_C @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) )
        = ( sk_C @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) )
        = ( sk_C @ X0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) )
        = ( sk_C @ X0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) )
        = ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t38_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r1_yellow_0 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
            & ( r2_yellow_0 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( r1_yellow_0 @ X27 @ ( k6_domain_1 @ ( u1_struct_0 @ X27 ) @ X26 ) )
      | ~ ( l1_orders_2 @ X27 )
      | ~ ( v5_orders_2 @ X27 )
      | ~ ( v3_orders_2 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ X21 @ X22 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k6_domain_1 @ X0 @ ( sk_C @ X1 @ X0 ) )
        = ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('40',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ~ ( v1_xboole_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_C @ X1 @ X0 ) )
        = ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(clc,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ X8 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_C @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fraenkel_a_2_2_waybel_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( l1_orders_2 @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
     => ( ( r2_hidden @ A @ ( a_2_2_waybel_0 @ B @ C ) )
      <=> ? [D: $i] :
            ( ( r1_yellow_0 @ B @ D )
            & ( A
              = ( k1_yellow_0 @ B @ D ) )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ C ) )
            & ( v1_finset_1 @ D ) ) ) ) )).

thf('51',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r2_hidden @ X13 @ ( a_2_2_waybel_0 @ X11 @ X12 ) )
      | ~ ( v1_finset_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X12 ) )
      | ( X13
       != ( k1_yellow_0 @ X11 @ X14 ) )
      | ~ ( r1_yellow_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_2_waybel_0])).

thf('52',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r1_yellow_0 @ X11 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( v1_finset_1 @ X14 )
      | ( r2_hidden @ ( k1_yellow_0 @ X11 @ X14 ) @ ( a_2_2_waybel_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( a_2_2_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( v1_finset_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d27_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k11_waybel_0 @ A @ B )
            = ( a_2_2_waybel_0 @ A @ B ) ) ) ) )).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( ( k11_waybel_0 @ X1 @ X0 )
        = ( a_2_2_waybel_0 @ X1 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d27_waybel_0])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k11_waybel_0 @ sk_A @ sk_B )
      = ( a_2_2_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k11_waybel_0 @ sk_A @ sk_B )
      = ( a_2_2_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k11_waybel_0 @ sk_A @ sk_B )
    = ( a_2_2_waybel_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( k11_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( v1_finset_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) )
      | ~ ( v1_finset_1 @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k11_waybel_0 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','62'])).

thf(fc1_finset_1,axiom,(
    ! [A: $i] :
      ( v1_finset_1 @ ( k1_tarski @ A ) ) )).

thf('64',plain,(
    ! [X10: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc1_finset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k11_waybel_0 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k11_waybel_0 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k11_waybel_0 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ sk_B @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k11_waybel_0 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ sk_B @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k11_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('71',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k11_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_B @ ( k11_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_B @ ( k11_waybel_0 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k11_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k11_waybel_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k11_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( r1_tarski @ sk_B @ ( k11_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('78',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ~ ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_B )
   <= ~ ( r1_tarski @ sk_B @ ( k11_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B @ X0 )
   <= ~ ( r1_tarski @ sk_B @ ( k11_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','80'])).

thf('82',plain,(
    r1_tarski @ sk_B @ ( k11_waybel_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','81'])).

thf('83',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k12_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ ( k11_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,(
    ~ ( r1_tarski @ sk_B @ ( k12_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( r1_tarski @ sk_B @ ( k12_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','84'])).

thf('86',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) )
        = ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('90',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( ( k2_yellow_0 @ X29 @ ( k6_domain_1 @ ( u1_struct_0 @ X29 ) @ X28 ) )
        = X28 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( ( k2_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) )
        = ( sk_C @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) )
        = ( sk_C @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k2_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) )
        = ( sk_C @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) )
        = ( sk_C @ X0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) )
        = ( sk_C @ X0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) )
        = ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('102',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( r2_yellow_0 @ X27 @ ( k6_domain_1 @ ( u1_struct_0 @ X27 ) @ X26 ) )
      | ~ ( l1_orders_2 @ X27 )
      | ~ ( v5_orders_2 @ X27 )
      | ~ ( v3_orders_2 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t38_yellow_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( r2_yellow_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['100','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('113',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fraenkel_a_2_3_waybel_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( l1_orders_2 @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
     => ( ( r2_hidden @ A @ ( a_2_3_waybel_0 @ B @ C ) )
      <=> ? [D: $i] :
            ( ( r2_yellow_0 @ B @ D )
            & ( A
              = ( k2_yellow_0 @ B @ D ) )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ C ) )
            & ( v1_finset_1 @ D ) ) ) ) )).

thf('114',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r2_hidden @ X17 @ ( a_2_3_waybel_0 @ X15 @ X16 ) )
      | ~ ( v1_finset_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X16 ) )
      | ( X17
       != ( k2_yellow_0 @ X15 @ X18 ) )
      | ~ ( r2_yellow_0 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_3_waybel_0])).

thf('115',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( r2_yellow_0 @ X15 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( v1_finset_1 @ X18 )
      | ( r2_hidden @ ( k2_yellow_0 @ X15 @ X18 ) @ ( a_2_3_waybel_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( a_2_3_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( v1_finset_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','115'])).

thf('117',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d28_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k12_waybel_0 @ A @ B )
            = ( a_2_3_waybel_0 @ A @ B ) ) ) ) )).

thf('119',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( ( k12_waybel_0 @ X3 @ X2 )
        = ( a_2_3_waybel_0 @ X3 @ X2 ) )
      | ~ ( l1_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d28_waybel_0])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k12_waybel_0 @ sk_A @ sk_B )
      = ( a_2_3_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k12_waybel_0 @ sk_A @ sk_B )
      = ( a_2_3_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( k12_waybel_0 @ sk_A @ sk_B )
    = ( a_2_3_waybel_0 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ X0 ) @ ( k12_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( v1_finset_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['116','117','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) )
      | ~ ( v1_finset_1 @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) )
      | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k12_waybel_0 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','125'])).

thf('127',plain,(
    ! [X10: $i] :
      ( v1_finset_1 @ ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc1_finset_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) )
      | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k12_waybel_0 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k12_waybel_0 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_yellow_0 @ sk_A @ ( k1_tarski @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k12_waybel_0 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ sk_B @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k12_waybel_0 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['99','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ sk_B @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k12_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('134',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k12_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_B @ ( k12_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_B @ ( k12_waybel_0 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k12_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( r1_tarski @ sk_B @ ( k12_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','84'])).

thf('139',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(demod,[status(thm)],['87','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['86','140'])).

thf('142',plain,(
    $false ),
    inference(demod,[status(thm)],['85','141'])).


%------------------------------------------------------------------------------

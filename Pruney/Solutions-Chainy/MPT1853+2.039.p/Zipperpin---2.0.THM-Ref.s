%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m6MBrdnfkP

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 297 expanded)
%              Number of leaves         :   34 (  95 expanded)
%              Depth                    :   20
%              Number of atoms          : 1230 (3608 expanded)
%              Number of equality atoms :   25 (  27 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(t20_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A )
          <=> ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A )
            <=> ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_tex_2])).

thf('0',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ X27 )
      | ( v1_subset_1 @ ( k6_domain_1 @ X27 @ X26 ) @ X27 )
      | ( v1_zfmisc_1 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_tex_2])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(cc1_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X1: $i] :
      ( ( v1_zfmisc_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_zfmisc_1])).

thf('8',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X16 @ X17 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('13',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( r1_tarski @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r1_tarski @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v1_zfmisc_1 @ X22 )
      | ( X23 = X22 )
      | ~ ( r1_tarski @ X23 @ X22 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('25',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('26',plain,
    ( ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('32',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('33',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('37',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['34','41'])).

thf(t15_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ~ ( ( ( u1_struct_0 @ B )
                = ( u1_struct_0 @ A ) )
              & ( v1_tex_2 @ B @ A ) ) ) ) )).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( ( u1_struct_0 @ X20 )
       != ( u1_struct_0 @ X21 ) )
      | ~ ( v1_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t15_tex_2])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( ( u1_struct_0 @ sk_A )
         != ( u1_struct_0 @ X0 ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
        | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
       != ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      & ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','44'])).

thf('46',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
       != ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      & ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      & ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('51',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      & ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      & ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('59',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf(d3_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( ( sk_C @ X11 @ X12 )
        = ( u1_struct_0 @ X11 ) )
      | ( v1_tex_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf('67',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_tex_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('71',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15 = X14 )
      | ( v1_subset_1 @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('72',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ~ ( v1_subset_1 @ ( sk_C @ X11 @ X12 ) @ ( u1_struct_0 @ X12 ) )
      | ( v1_tex_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('74',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf('77',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('80',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['65','80'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('82',plain,(
    ! [X6: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ~ ( v7_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('83',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ) )).

thf('85',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('86',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('92',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['83','90','91'])).

thf('93',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t6_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf('94',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ X25 )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ X25 @ X24 ) @ X25 )
      | ~ ( v1_zfmisc_1 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t6_tex_2])).

thf('95',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('100',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','57','58','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m6MBrdnfkP
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:15:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 81 iterations in 0.043s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.50  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.22/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.50  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.22/0.50  thf(t20_tex_2, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.50           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.22/0.50             ( v1_subset_1 @
% 0.22/0.50               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.50              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.22/0.50                ( v1_subset_1 @
% 0.22/0.50                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.22/0.50                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.50           (u1_struct_0 @ sk_A))
% 0.22/0.50        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (~
% 0.22/0.50       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.50         (u1_struct_0 @ sk_A))) | 
% 0.22/0.50       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.50         (u1_struct_0 @ sk_A))
% 0.22/0.50        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.22/0.50         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['2'])).
% 0.22/0.50  thf('4', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t7_tex_2, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.50           ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) ))).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X26 : $i, X27 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X26 @ X27)
% 0.22/0.50          | (v1_subset_1 @ (k6_domain_1 @ X27 @ X26) @ X27)
% 0.22/0.50          | (v1_zfmisc_1 @ X27)
% 0.22/0.50          | (v1_xboole_0 @ X27))),
% 0.22/0.50      inference('cnf', [status(esa)], [t7_tex_2])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.50        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.50        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.50           (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.50  thf(cc1_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_zfmisc_1 @ A ) ))).
% 0.22/0.50  thf('7', plain, (![X1 : $i]: ((v1_zfmisc_1 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc1_zfmisc_1])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.50         (u1_struct_0 @ sk_A))
% 0.22/0.50        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('clc', [status(thm)], ['6', '7'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.50           (u1_struct_0 @ sk_A)))
% 0.22/0.50         <= (~
% 0.22/0.50             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.50               (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.50         <= (~
% 0.22/0.50             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.50               (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(dt_k1_tex_2, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.22/0.50         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.22/0.50         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.22/0.50         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ X16)
% 0.22/0.50          | (v2_struct_0 @ X16)
% 0.22/0.50          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.22/0.50          | (m1_pre_topc @ (k1_tex_2 @ X16 @ X17) @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.50  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.50  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('17', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.50      inference('clc', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf(t35_borsuk_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.50           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (![X9 : $i, X10 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X9 @ X10)
% 0.22/0.51          | (r1_tarski @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X10))
% 0.22/0.51          | ~ (l1_pre_topc @ X10))),
% 0.22/0.51      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | (r1_tarski @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.22/0.51           (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.51  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      ((r1_tarski @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.22/0.51        (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.51  thf(t1_tex_2, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.22/0.51           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (![X22 : $i, X23 : $i]:
% 0.22/0.51         ((v1_xboole_0 @ X22)
% 0.22/0.51          | ~ (v1_zfmisc_1 @ X22)
% 0.22/0.51          | ((X23) = (X22))
% 0.22/0.51          | ~ (r1_tarski @ X23 @ X22)
% 0.22/0.51          | (v1_xboole_0 @ X23))),
% 0.22/0.51      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))
% 0.22/0.51        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.22/0.51        | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51         | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.22/0.51         | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))))
% 0.22/0.51         <= (~
% 0.22/0.51             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51               (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['10', '23'])).
% 0.22/0.51  thf(fc2_struct_0, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.51       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      (![X5 : $i]:
% 0.22/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X5))
% 0.22/0.51          | ~ (l1_struct_0 @ X5)
% 0.22/0.51          | (v2_struct_0 @ X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      (((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.22/0.51         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51         | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.51         | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.22/0.51         <= (~
% 0.22/0.51             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51               (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.51  thf('27', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.51      inference('clc', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf(dt_m1_pre_topc, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.51  thf('28', plain,
% 0.22/0.51      (![X3 : $i, X4 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.51  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('31', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.51  thf(dt_l1_pre_topc, axiom,
% 0.22/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.51  thf('32', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf('33', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      (((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.22/0.51         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51         | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.22/0.51         <= (~
% 0.22/0.51             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51               (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['26', '33'])).
% 0.22/0.51  thf('35', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      (![X16 : $i, X17 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ X16)
% 0.22/0.51          | (v2_struct_0 @ X16)
% 0.22/0.51          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.22/0.51          | ~ (v2_struct_0 @ (k1_tex_2 @ X16 @ X17)))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.22/0.51  thf('37', plain,
% 0.22/0.51      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.51  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('39', plain,
% 0.22/0.51      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['37', '38'])).
% 0.22/0.51  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('41', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.22/0.51      inference('clc', [status(thm)], ['39', '40'])).
% 0.22/0.51  thf('42', plain,
% 0.22/0.51      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51         | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))))
% 0.22/0.51         <= (~
% 0.22/0.51             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51               (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('clc', [status(thm)], ['34', '41'])).
% 0.22/0.51  thf(t15_tex_2, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.51           ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.22/0.51                ( v1_tex_2 @ B @ A ) ) ) ) ) ))).
% 0.22/0.51  thf('43', plain,
% 0.22/0.51      (![X20 : $i, X21 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X20 @ X21)
% 0.22/0.51          | ((u1_struct_0 @ X20) != (u1_struct_0 @ X21))
% 0.22/0.51          | ~ (v1_tex_2 @ X20 @ X21)
% 0.22/0.51          | ~ (l1_pre_topc @ X21))),
% 0.22/0.51      inference('cnf', [status(esa)], [t15_tex_2])).
% 0.22/0.51  thf('44', plain,
% 0.22/0.51      ((![X0 : $i]:
% 0.22/0.51          (((u1_struct_0 @ sk_A) != (u1_struct_0 @ X0))
% 0.22/0.51           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51           | ~ (l1_pre_topc @ X0)
% 0.22/0.51           | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.22/0.51           | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)))
% 0.22/0.51         <= (~
% 0.22/0.51             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51               (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.22/0.51  thf('45', plain,
% 0.22/0.51      (((~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.51         | ~ (l1_pre_topc @ sk_A)
% 0.22/0.51         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51         | ((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))))
% 0.22/0.51         <= (~
% 0.22/0.51             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51               (u1_struct_0 @ sk_A))) & 
% 0.22/0.51             ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['3', '44'])).
% 0.22/0.51  thf('46', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.51      inference('clc', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('48', plain,
% 0.22/0.51      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51         | ((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))))
% 0.22/0.51         <= (~
% 0.22/0.51             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51               (u1_struct_0 @ sk_A))) & 
% 0.22/0.51             ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.22/0.51  thf('49', plain,
% 0.22/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51         <= (~
% 0.22/0.51             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51               (u1_struct_0 @ sk_A))) & 
% 0.22/0.51             ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['48'])).
% 0.22/0.51  thf('50', plain,
% 0.22/0.51      (![X5 : $i]:
% 0.22/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X5))
% 0.22/0.51          | ~ (l1_struct_0 @ X5)
% 0.22/0.51          | (v2_struct_0 @ X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.51  thf('51', plain,
% 0.22/0.51      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.22/0.51         <= (~
% 0.22/0.51             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51               (u1_struct_0 @ sk_A))) & 
% 0.22/0.51             ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.51  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('53', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.51  thf('55', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_A))
% 0.22/0.51         <= (~
% 0.22/0.51             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51               (u1_struct_0 @ sk_A))) & 
% 0.22/0.51             ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['51', '54'])).
% 0.22/0.51  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('57', plain,
% 0.22/0.51      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51         (u1_struct_0 @ sk_A))) | 
% 0.22/0.51       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.51  thf('58', plain,
% 0.22/0.51      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51         (u1_struct_0 @ sk_A))) | 
% 0.22/0.51       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf('59', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.51      inference('clc', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf(d3_tex_2, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.51           ( ( v1_tex_2 @ B @ A ) <=>
% 0.22/0.51             ( ![C:$i]:
% 0.22/0.51               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.22/0.51                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('60', plain,
% 0.22/0.51      (![X11 : $i, X12 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X11 @ X12)
% 0.22/0.51          | ((sk_C @ X11 @ X12) = (u1_struct_0 @ X11))
% 0.22/0.51          | (v1_tex_2 @ X11 @ X12)
% 0.22/0.51          | ~ (l1_pre_topc @ X12))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.22/0.51  thf('61', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.51        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.51            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.51  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('63', plain,
% 0.22/0.51      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.51        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.51            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))),
% 0.22/0.51      inference('demod', [status(thm)], ['61', '62'])).
% 0.22/0.51  thf('64', plain,
% 0.22/0.51      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.22/0.51         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('65', plain,
% 0.22/0.51      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.51          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.22/0.51         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['63', '64'])).
% 0.22/0.51  thf('66', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.51      inference('clc', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('67', plain,
% 0.22/0.51      (![X11 : $i, X12 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X11 @ X12)
% 0.22/0.51          | (m1_subset_1 @ (sk_C @ X11 @ X12) @ 
% 0.22/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.51          | (v1_tex_2 @ X11 @ X12)
% 0.22/0.51          | ~ (l1_pre_topc @ X12))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.22/0.51  thf('68', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.51        | (m1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) @ 
% 0.22/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['66', '67'])).
% 0.22/0.51  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('70', plain,
% 0.22/0.51      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.51        | (m1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) @ 
% 0.22/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['68', '69'])).
% 0.22/0.51  thf(d7_subset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.51       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.22/0.51  thf('71', plain,
% 0.22/0.51      (![X14 : $i, X15 : $i]:
% 0.22/0.51         (((X15) = (X14))
% 0.22/0.51          | (v1_subset_1 @ X15 @ X14)
% 0.22/0.51          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.22/0.51      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.22/0.51  thf('72', plain,
% 0.22/0.51      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.51        | (v1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) @ 
% 0.22/0.51           (u1_struct_0 @ sk_A))
% 0.22/0.51        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['70', '71'])).
% 0.22/0.51  thf('73', plain,
% 0.22/0.51      (![X11 : $i, X12 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X11 @ X12)
% 0.22/0.51          | ~ (v1_subset_1 @ (sk_C @ X11 @ X12) @ (u1_struct_0 @ X12))
% 0.22/0.51          | (v1_tex_2 @ X11 @ X12)
% 0.22/0.51          | ~ (l1_pre_topc @ X12))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.22/0.51  thf('74', plain,
% 0.22/0.51      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) = (u1_struct_0 @ sk_A))
% 0.22/0.51        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.51        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['72', '73'])).
% 0.22/0.51  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('76', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.51      inference('clc', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('77', plain,
% 0.22/0.51      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) = (u1_struct_0 @ sk_A))
% 0.22/0.51        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.51        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.22/0.51  thf('78', plain,
% 0.22/0.51      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.51        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['77'])).
% 0.22/0.51  thf('79', plain,
% 0.22/0.51      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.22/0.51         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('80', plain,
% 0.22/0.51      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) = (u1_struct_0 @ sk_A)))
% 0.22/0.51         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['78', '79'])).
% 0.22/0.51  thf('81', plain,
% 0.22/0.51      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))
% 0.22/0.51         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['65', '80'])).
% 0.22/0.51  thf(fc7_struct_0, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.51       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.22/0.51  thf('82', plain,
% 0.22/0.51      (![X6 : $i]:
% 0.22/0.51         ((v1_zfmisc_1 @ (u1_struct_0 @ X6))
% 0.22/0.51          | ~ (l1_struct_0 @ X6)
% 0.22/0.51          | ~ (v7_struct_0 @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.22/0.51  thf('83', plain,
% 0.22/0.51      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.51         | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.51         | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.22/0.51         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['81', '82'])).
% 0.22/0.51  thf('84', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(fc2_tex_2, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.22/0.51         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.22/0.51         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.22/0.51         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.22/0.51  thf('85', plain,
% 0.22/0.51      (![X18 : $i, X19 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ X18)
% 0.22/0.51          | (v2_struct_0 @ X18)
% 0.22/0.51          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.22/0.51          | (v7_struct_0 @ (k1_tex_2 @ X18 @ X19)))),
% 0.22/0.51      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.22/0.51  thf('86', plain,
% 0.22/0.51      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.51        | (v2_struct_0 @ sk_A)
% 0.22/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['84', '85'])).
% 0.22/0.51  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('88', plain,
% 0.22/0.51      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['86', '87'])).
% 0.22/0.51  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('90', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.22/0.51      inference('clc', [status(thm)], ['88', '89'])).
% 0.22/0.51  thf('91', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.51  thf('92', plain,
% 0.22/0.51      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['83', '90', '91'])).
% 0.22/0.51  thf('93', plain,
% 0.22/0.51      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51         (u1_struct_0 @ sk_A)))
% 0.22/0.51         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51               (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf(t6_tex_2, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.51           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.22/0.51                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.22/0.51  thf('94', plain,
% 0.22/0.51      (![X24 : $i, X25 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X24 @ X25)
% 0.22/0.51          | ~ (v1_subset_1 @ (k6_domain_1 @ X25 @ X24) @ X25)
% 0.22/0.51          | ~ (v1_zfmisc_1 @ X25)
% 0.22/0.51          | (v1_xboole_0 @ X25))),
% 0.22/0.51      inference('cnf', [status(esa)], [t6_tex_2])).
% 0.22/0.51  thf('95', plain,
% 0.22/0.51      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51         | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.51         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.22/0.51         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51               (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['93', '94'])).
% 0.22/0.51  thf('96', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('97', plain,
% 0.22/0.51      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51         | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.51         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51               (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['95', '96'])).
% 0.22/0.51  thf('98', plain,
% 0.22/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)) & 
% 0.22/0.51             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51               (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['92', '97'])).
% 0.22/0.51  thf('99', plain,
% 0.22/0.51      (![X5 : $i]:
% 0.22/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X5))
% 0.22/0.51          | ~ (l1_struct_0 @ X5)
% 0.22/0.51          | (v2_struct_0 @ X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.51  thf('100', plain,
% 0.22/0.51      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.22/0.51         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)) & 
% 0.22/0.51             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51               (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['98', '99'])).
% 0.22/0.51  thf('101', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.51  thf('102', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_A))
% 0.22/0.51         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)) & 
% 0.22/0.51             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51               (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['100', '101'])).
% 0.22/0.51  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('104', plain,
% 0.22/0.51      (~
% 0.22/0.51       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51         (u1_struct_0 @ sk_A))) | 
% 0.22/0.51       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['102', '103'])).
% 0.22/0.51  thf('105', plain, ($false),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['1', '57', '58', '104'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

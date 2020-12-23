%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gKEYPQnO73

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 451 expanded)
%              Number of leaves         :   33 ( 136 expanded)
%              Depth                    :   20
%              Number of atoms          : 1228 (5868 expanded)
%              Number of equality atoms :   27 (  57 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

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
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ X25 )
      | ( v1_subset_1 @ ( k6_domain_1 @ X25 @ X24 ) @ X25 )
      | ( v1_zfmisc_1 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
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
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
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
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
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

thf('59',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('60',plain,(
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

thf('61',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( ( sk_C @ X11 @ X12 )
        = ( u1_struct_0 @ X11 ) )
      | ( v1_tex_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf('68',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_tex_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('72',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15 = X14 )
      | ( v1_subset_1 @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('73',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ~ ( v1_subset_1 @ ( sk_C @ X11 @ X12 ) @ ( u1_struct_0 @ X12 ) )
      | ( v1_tex_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('75',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf('78',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('81',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['66','81'])).

thf(t8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) )
              & ( v7_struct_0 @ A ) ) ) ) )).

thf('83',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X27 ) @ X26 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v7_struct_0 @ X27 )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_tex_2])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['66','81'])).

thf('86',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('87',plain,(
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

thf('88',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('89',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['66','81'])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86','93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','57','58','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gKEYPQnO73
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:21:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 92 iterations in 0.049s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.55  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.55  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.55  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.55  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.55  thf(t20_tex_2, conjecture,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.21/0.55             ( v1_subset_1 @
% 0.21/0.55               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i]:
% 0.21/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55          ( ![B:$i]:
% 0.21/0.55            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.21/0.55                ( v1_subset_1 @
% 0.21/0.55                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.21/0.55                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55           (u1_struct_0 @ sk_A))
% 0.21/0.55        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (~
% 0.21/0.55       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55         (u1_struct_0 @ sk_A))) | 
% 0.21/0.55       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55         (u1_struct_0 @ sk_A))
% 0.21/0.55        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.21/0.55         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['2'])).
% 0.21/0.55  thf('4', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t7_tex_2, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.55           ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) ))).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X24 : $i, X25 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X24 @ X25)
% 0.21/0.55          | (v1_subset_1 @ (k6_domain_1 @ X25 @ X24) @ X25)
% 0.21/0.55          | (v1_zfmisc_1 @ X25)
% 0.21/0.55          | (v1_xboole_0 @ X25))),
% 0.21/0.55      inference('cnf', [status(esa)], [t7_tex_2])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.55        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55           (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf(cc1_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_zfmisc_1 @ A ) ))).
% 0.21/0.55  thf('7', plain, (![X1 : $i]: ((v1_zfmisc_1 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc1_zfmisc_1])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55         (u1_struct_0 @ sk_A))
% 0.21/0.55        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55           (u1_struct_0 @ sk_A)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55               (u1_struct_0 @ sk_A))))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55               (u1_struct_0 @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(dt_k1_tex_2, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.21/0.55         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.21/0.55         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.21/0.55         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X16)
% 0.21/0.55          | (v2_struct_0 @ X16)
% 0.21/0.55          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.21/0.55          | (m1_pre_topc @ (k1_tex_2 @ X16 @ X17) @ X16))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.55  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.55  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('17', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.55      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf(t35_borsuk_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.55           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i]:
% 0.21/0.55         (~ (m1_pre_topc @ X9 @ X10)
% 0.21/0.55          | (r1_tarski @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X10))
% 0.21/0.55          | ~ (l1_pre_topc @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (r1_tarski @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.21/0.55           (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.55  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      ((r1_tarski @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.21/0.55        (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.55  thf(t1_tex_2, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.55           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X22 : $i, X23 : $i]:
% 0.21/0.55         ((v1_xboole_0 @ X22)
% 0.21/0.55          | ~ (v1_zfmisc_1 @ X22)
% 0.21/0.55          | ((X23) = (X22))
% 0.21/0.55          | ~ (r1_tarski @ X23 @ X22)
% 0.21/0.55          | (v1_xboole_0 @ X23))),
% 0.21/0.55      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))
% 0.21/0.55        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.21/0.55        | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55         | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.21/0.55         | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55               (u1_struct_0 @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['10', '23'])).
% 0.21/0.55  thf(fc2_struct_0, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.55       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X6 : $i]:
% 0.21/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X6))
% 0.21/0.55          | ~ (l1_struct_0 @ X6)
% 0.21/0.55          | (v2_struct_0 @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.21/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55         | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.55         | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55               (u1_struct_0 @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.55  thf('27', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.55      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf(dt_m1_pre_topc, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i]:
% 0.21/0.55         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.55  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('31', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.55  thf(dt_l1_pre_topc, axiom,
% 0.21/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.55  thf('32', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.55  thf('33', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.21/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55         | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55               (u1_struct_0 @ sk_A))))),
% 0.21/0.55      inference('demod', [status(thm)], ['26', '33'])).
% 0.21/0.55  thf('35', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X16)
% 0.21/0.55          | (v2_struct_0 @ X16)
% 0.21/0.55          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.21/0.55          | ~ (v2_struct_0 @ (k1_tex_2 @ X16 @ X17)))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.55  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.55  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('41', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.55      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55         | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55               (u1_struct_0 @ sk_A))))),
% 0.21/0.55      inference('clc', [status(thm)], ['34', '41'])).
% 0.21/0.55  thf(t15_tex_2, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.55           ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.21/0.55                ( v1_tex_2 @ B @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      (![X20 : $i, X21 : $i]:
% 0.21/0.55         (~ (m1_pre_topc @ X20 @ X21)
% 0.21/0.55          | ((u1_struct_0 @ X20) != (u1_struct_0 @ X21))
% 0.21/0.55          | ~ (v1_tex_2 @ X20 @ X21)
% 0.21/0.55          | ~ (l1_pre_topc @ X21))),
% 0.21/0.55      inference('cnf', [status(esa)], [t15_tex_2])).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      ((![X0 : $i]:
% 0.21/0.55          (((u1_struct_0 @ sk_A) != (u1_struct_0 @ X0))
% 0.21/0.55           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55           | ~ (l1_pre_topc @ X0)
% 0.21/0.55           | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.21/0.55           | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55               (u1_struct_0 @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      (((~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.55         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55         | ((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55               (u1_struct_0 @ sk_A))) & 
% 0.21/0.55             ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['3', '44'])).
% 0.21/0.55  thf('46', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.55      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('48', plain,
% 0.21/0.55      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55         | ((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55               (u1_struct_0 @ sk_A))) & 
% 0.21/0.55             ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55               (u1_struct_0 @ sk_A))) & 
% 0.21/0.55             ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      (![X6 : $i]:
% 0.21/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X6))
% 0.21/0.55          | ~ (l1_struct_0 @ X6)
% 0.21/0.55          | (v2_struct_0 @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55               (u1_struct_0 @ sk_A))) & 
% 0.21/0.55             ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.55  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('53', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.55  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A))
% 0.21/0.55         <= (~
% 0.21/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55               (u1_struct_0 @ sk_A))) & 
% 0.21/0.55             ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['51', '54'])).
% 0.21/0.55  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('57', plain,
% 0.21/0.55      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55         (u1_struct_0 @ sk_A))) | 
% 0.21/0.55       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.55  thf('58', plain,
% 0.21/0.55      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55         (u1_struct_0 @ sk_A))) | 
% 0.21/0.55       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.55      inference('split', [status(esa)], ['2'])).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55         (u1_struct_0 @ sk_A)))
% 0.21/0.55         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55               (u1_struct_0 @ sk_A))))),
% 0.21/0.55      inference('split', [status(esa)], ['2'])).
% 0.21/0.55  thf('60', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.55      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf(d3_tex_2, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.55           ( ( v1_tex_2 @ B @ A ) <=>
% 0.21/0.55             ( ![C:$i]:
% 0.21/0.55               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.55                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf('61', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i]:
% 0.21/0.55         (~ (m1_pre_topc @ X11 @ X12)
% 0.21/0.55          | ((sk_C @ X11 @ X12) = (u1_struct_0 @ X11))
% 0.21/0.55          | (v1_tex_2 @ X11 @ X12)
% 0.21/0.55          | ~ (l1_pre_topc @ X12))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.55  thf('62', plain,
% 0.21/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.55        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.55            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.55  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('64', plain,
% 0.21/0.55      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.55        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.55            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))),
% 0.21/0.55      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.55  thf('65', plain,
% 0.21/0.55      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.21/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('66', plain,
% 0.21/0.55      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.55          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.21/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.55  thf('67', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.55      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('68', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i]:
% 0.21/0.55         (~ (m1_pre_topc @ X11 @ X12)
% 0.21/0.55          | (m1_subset_1 @ (sk_C @ X11 @ X12) @ 
% 0.21/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.55          | (v1_tex_2 @ X11 @ X12)
% 0.21/0.55          | ~ (l1_pre_topc @ X12))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.55  thf('69', plain,
% 0.21/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.55        | (m1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.55  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('71', plain,
% 0.21/0.55      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.55        | (m1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.55      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.55  thf(d7_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.21/0.55  thf('72', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i]:
% 0.21/0.55         (((X15) = (X14))
% 0.21/0.55          | (v1_subset_1 @ X15 @ X14)
% 0.21/0.55          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.55  thf('73', plain,
% 0.21/0.55      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.55        | (v1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) @ 
% 0.21/0.55           (u1_struct_0 @ sk_A))
% 0.21/0.55        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.55  thf('74', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i]:
% 0.21/0.55         (~ (m1_pre_topc @ X11 @ X12)
% 0.21/0.55          | ~ (v1_subset_1 @ (sk_C @ X11 @ X12) @ (u1_struct_0 @ X12))
% 0.21/0.55          | (v1_tex_2 @ X11 @ X12)
% 0.21/0.55          | ~ (l1_pre_topc @ X12))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.55  thf('75', plain,
% 0.21/0.55      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) = (u1_struct_0 @ sk_A))
% 0.21/0.55        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.55        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.55  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('77', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.55      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('78', plain,
% 0.21/0.55      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) = (u1_struct_0 @ sk_A))
% 0.21/0.55        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.55        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.21/0.55  thf('79', plain,
% 0.21/0.55      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.55        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['78'])).
% 0.21/0.55  thf('80', plain,
% 0.21/0.55      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.21/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('81', plain,
% 0.21/0.55      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) = (u1_struct_0 @ sk_A)))
% 0.21/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['79', '80'])).
% 0.21/0.55  thf('82', plain,
% 0.21/0.55      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))
% 0.21/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['66', '81'])).
% 0.21/0.55  thf(t8_tex_2, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55           ( ~( ( v1_subset_1 @
% 0.21/0.55                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.21/0.55                  ( u1_struct_0 @ A ) ) & 
% 0.21/0.55                ( v7_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('83', plain,
% 0.21/0.55      (![X26 : $i, X27 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.21/0.55          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X27) @ X26) @ 
% 0.21/0.55               (u1_struct_0 @ X27))
% 0.21/0.55          | ~ (v7_struct_0 @ X27)
% 0.21/0.55          | ~ (l1_struct_0 @ X27)
% 0.21/0.55          | (v2_struct_0 @ X27))),
% 0.21/0.55      inference('cnf', [status(esa)], [t8_tex_2])).
% 0.21/0.55  thf('84', plain,
% 0.21/0.55      ((![X0 : $i]:
% 0.21/0.55          (~ (v1_subset_1 @ 
% 0.21/0.55              (k6_domain_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ X0) @ 
% 0.21/0.55              (u1_struct_0 @ sk_A))
% 0.21/0.55           | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.55           | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.55           | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.55           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))))
% 0.21/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['82', '83'])).
% 0.21/0.55  thf('85', plain,
% 0.21/0.55      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))
% 0.21/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['66', '81'])).
% 0.21/0.55  thf('86', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.55  thf('87', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(fc2_tex_2, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.21/0.55         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.21/0.55         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.21/0.55         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.21/0.55  thf('88', plain,
% 0.21/0.55      (![X18 : $i, X19 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X18)
% 0.21/0.55          | (v2_struct_0 @ X18)
% 0.21/0.55          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.21/0.55          | (v7_struct_0 @ (k1_tex_2 @ X18 @ X19)))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.21/0.55  thf('89', plain,
% 0.21/0.55      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['87', '88'])).
% 0.21/0.55  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('91', plain,
% 0.21/0.55      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['89', '90'])).
% 0.21/0.55  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('93', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.55      inference('clc', [status(thm)], ['91', '92'])).
% 0.21/0.55  thf('94', plain,
% 0.21/0.55      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))
% 0.21/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['66', '81'])).
% 0.21/0.55  thf('95', plain,
% 0.21/0.55      ((![X0 : $i]:
% 0.21/0.55          (~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.21/0.55              (u1_struct_0 @ sk_A))
% 0.21/0.55           | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.55           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['84', '85', '86', '93', '94'])).
% 0.21/0.55  thf('96', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.55      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.55  thf('97', plain,
% 0.21/0.55      ((![X0 : $i]:
% 0.21/0.55          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55           | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.21/0.55                (u1_struct_0 @ sk_A))))
% 0.21/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('clc', [status(thm)], ['95', '96'])).
% 0.21/0.55  thf('98', plain,
% 0.21/0.55      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.21/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)) & 
% 0.21/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55               (u1_struct_0 @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['59', '97'])).
% 0.21/0.55  thf('99', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('100', plain,
% 0.21/0.55      (~
% 0.21/0.55       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55         (u1_struct_0 @ sk_A))) | 
% 0.21/0.55       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['98', '99'])).
% 0.21/0.55  thf('101', plain, ($false),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['1', '57', '58', '100'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

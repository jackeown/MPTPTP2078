%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fw2ctp2Bn5

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:39 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 151 expanded)
%              Number of leaves         :   29 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  692 (2216 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t20_compts_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v8_pre_topc @ A )
                  & ( v2_compts_1 @ B @ A )
                  & ( v2_compts_1 @ C @ A ) )
               => ( v2_compts_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v8_pre_topc @ A )
                    & ( v2_compts_1 @ B @ A )
                    & ( v2_compts_1 @ C @ A ) )
                 => ( v2_compts_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_compts_1])).

thf('0',plain,(
    ~ ( v2_compts_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X8 @ X6 @ X7 )
        = ( k3_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( v4_pre_topc @ C @ A ) )
               => ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v4_pre_topc @ X21 @ X22 )
      | ~ ( v4_pre_topc @ X23 @ X22 )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 @ X23 ) @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t35_tops_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_compts_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v8_pre_topc @ A )
              & ( v2_compts_1 @ B @ A ) )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v4_pre_topc @ X24 @ X25 )
      | ~ ( v2_compts_1 @ X24 @ X25 )
      | ~ ( v8_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('13',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10','18'])).

thf('20',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v4_pre_topc @ X24 @ X25 )
      | ~ ( v2_compts_1 @ X24 @ X25 )
      | ~ ( v8_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('23',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_C @ sk_A )
    | ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('30',plain,(
    v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['20','28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X14 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('33',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['33','34'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ( m1_subset_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('45',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X17 @ X16 ) )
        = X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_compts_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v2_compts_1 @ B @ A )
                  & ( r1_tarski @ C @ B )
                  & ( v4_pre_topc @ C @ A ) )
               => ( v2_compts_1 @ C @ A ) ) ) ) ) )).

thf('52',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_compts_1 @ X26 @ X27 )
      | ~ ( r1_tarski @ X28 @ X26 )
      | ~ ( v4_pre_topc @ X28 @ X27 )
      | ( v2_compts_1 @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t18_compts_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_compts_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['30','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['4','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fw2ctp2Bn5
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 270 iterations in 0.206s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.46/0.66  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.46/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.66  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.66  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.46/0.66  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.46/0.66  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.46/0.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(t20_compts_1, conjecture,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66               ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.46/0.66                   ( v2_compts_1 @ C @ A ) ) =>
% 0.46/0.66                 ( v2_compts_1 @
% 0.46/0.66                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i]:
% 0.46/0.66        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66          ( ![B:$i]:
% 0.46/0.66            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66              ( ![C:$i]:
% 0.46/0.66                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66                  ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.46/0.66                      ( v2_compts_1 @ C @ A ) ) =>
% 0.46/0.66                    ( v2_compts_1 @
% 0.46/0.66                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t20_compts_1])).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      (~ (v2_compts_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.66          sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(redefinition_k9_subset_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.66       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.66         (((k9_subset_1 @ X8 @ X6 @ X7) = (k3_xboole_0 @ X6 @ X7))
% 0.46/0.66          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.46/0.66           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.66  thf('4', plain, (~ (v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.46/0.66      inference('demod', [status(thm)], ['0', '3'])).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(t35_tops_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.46/0.66                 ( v4_pre_topc @
% 0.46/0.66                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.46/0.66          | ~ (v4_pre_topc @ X21 @ X22)
% 0.46/0.66          | ~ (v4_pre_topc @ X23 @ X22)
% 0.46/0.66          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ X22) @ X21 @ X23) @ 
% 0.46/0.66             X22)
% 0.46/0.66          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.46/0.66          | ~ (l1_pre_topc @ X22)
% 0.46/0.66          | ~ (v2_pre_topc @ X22))),
% 0.46/0.66      inference('cnf', [status(esa)], [t35_tops_1])).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v2_pre_topc @ sk_A)
% 0.46/0.66          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.46/0.66             sk_A)
% 0.46/0.66          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.46/0.66          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(t16_compts_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.46/0.66             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X24 : $i, X25 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.46/0.66          | (v4_pre_topc @ X24 @ X25)
% 0.46/0.66          | ~ (v2_compts_1 @ X24 @ X25)
% 0.46/0.66          | ~ (v8_pre_topc @ X25)
% 0.46/0.66          | ~ (l1_pre_topc @ X25)
% 0.46/0.66          | ~ (v2_pre_topc @ X25))),
% 0.46/0.66      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      ((~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | ~ (v8_pre_topc @ sk_A)
% 0.46/0.66        | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.46/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.66  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('16', plain, ((v8_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('17', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('18', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.46/0.66      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.46/0.66             sk_A)
% 0.46/0.66          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['8', '9', '10', '18'])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      ((~ (v4_pre_topc @ sk_C @ sk_A)
% 0.46/0.66        | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.66           sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['5', '19'])).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('22', plain,
% 0.46/0.66      (![X24 : $i, X25 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.46/0.66          | (v4_pre_topc @ X24 @ X25)
% 0.46/0.66          | ~ (v2_compts_1 @ X24 @ X25)
% 0.46/0.66          | ~ (v8_pre_topc @ X25)
% 0.46/0.66          | ~ (l1_pre_topc @ X25)
% 0.46/0.66          | ~ (v2_pre_topc @ X25))),
% 0.46/0.66      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      ((~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | ~ (v8_pre_topc @ sk_A)
% 0.46/0.66        | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.46/0.66        | (v4_pre_topc @ sk_C @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('26', plain, ((v8_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('27', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('28', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.46/0.66      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.46/0.66           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.66  thf('30', plain, ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.46/0.66      inference('demod', [status(thm)], ['20', '28', '29'])).
% 0.46/0.66  thf('31', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(dt_k1_pre_topc, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( l1_pre_topc @ A ) & 
% 0.46/0.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.66       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.46/0.66         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X14)
% 0.46/0.66          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.46/0.66          | (m1_pre_topc @ (k1_pre_topc @ X14 @ X15) @ X14))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.66  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('35', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.46/0.66      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.66  thf(t48_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.66  thf('36', plain,
% 0.46/0.66      (![X2 : $i, X3 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.46/0.66           = (k3_xboole_0 @ X2 @ X3))),
% 0.46/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.66  thf(t36_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.46/0.66      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.46/0.66      inference('sup+', [status(thm)], ['36', '37'])).
% 0.46/0.66  thf(t3_subset, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      (![X11 : $i, X13 : $i]:
% 0.46/0.66         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf(t39_pre_topc, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.46/0.66               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.66         (~ (m1_pre_topc @ X18 @ X19)
% 0.46/0.66          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.46/0.66          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.46/0.66          | ~ (l1_pre_topc @ X19))),
% 0.46/0.66      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X2)
% 0.46/0.66          | (m1_subset_1 @ (k3_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ 
% 0.46/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.46/0.66          | ~ (m1_pre_topc @ X0 @ X2))),
% 0.46/0.66      inference('sup-', [status(thm)], ['40', '41'])).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((m1_subset_1 @ 
% 0.46/0.66           (k3_xboole_0 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ X0) @ 
% 0.46/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['35', '42'])).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(t29_pre_topc, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 0.46/0.66  thf('45', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.46/0.66          | ((u1_struct_0 @ (k1_pre_topc @ X17 @ X16)) = (X16))
% 0.46/0.66          | ~ (l1_pre_topc @ X17))),
% 0.46/0.66      inference('cnf', [status(esa)], [t29_pre_topc])).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.66  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('48', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.66  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('50', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.46/0.66          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['43', '48', '49'])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(t18_compts_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.46/0.66                   ( v4_pre_topc @ C @ A ) ) =>
% 0.46/0.66                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.66          | ~ (v2_compts_1 @ X26 @ X27)
% 0.46/0.66          | ~ (r1_tarski @ X28 @ X26)
% 0.46/0.66          | ~ (v4_pre_topc @ X28 @ X27)
% 0.46/0.66          | (v2_compts_1 @ X28 @ X27)
% 0.46/0.66          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.66          | ~ (l1_pre_topc @ X27)
% 0.46/0.66          | ~ (v2_pre_topc @ X27))),
% 0.46/0.66      inference('cnf', [status(esa)], [t18_compts_1])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v2_pre_topc @ sk_A)
% 0.46/0.66          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | (v2_compts_1 @ X0 @ sk_A)
% 0.46/0.66          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.46/0.66          | ~ (r1_tarski @ X0 @ sk_B)
% 0.46/0.66          | ~ (v2_compts_1 @ sk_B @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['51', '52'])).
% 0.46/0.66  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('56', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('57', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | (v2_compts_1 @ X0 @ sk_A)
% 0.46/0.66          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.46/0.66          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.46/0.66  thf('58', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)
% 0.46/0.66          | ~ (v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.46/0.66          | (v2_compts_1 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['50', '57'])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.46/0.66      inference('sup+', [status(thm)], ['36', '37'])).
% 0.46/0.66  thf('60', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.46/0.66          | (v2_compts_1 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['58', '59'])).
% 0.46/0.66  thf('61', plain, ((v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.46/0.66      inference('sup-', [status(thm)], ['30', '60'])).
% 0.46/0.66  thf('62', plain, ($false), inference('demod', [status(thm)], ['4', '61'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

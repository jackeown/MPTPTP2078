%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hxuencl2jZ

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:39 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 145 expanded)
%              Number of leaves         :   29 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  673 (2110 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf(fc4_tops_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v4_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( v4_pre_topc @ C @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k3_xboole_0 @ B @ C ) @ A ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v4_pre_topc @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( v4_pre_topc @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v4_pre_topc @ ( k3_xboole_0 @ X21 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc4_tops_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
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
      ( ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10','18'])).

thf('20',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
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
    v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['20','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X14 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('32',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['32','33'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ( m1_subset_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X17 @ X16 ) )
        = X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','47','48'])).

thf('50',plain,(
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

thf('51',plain,(
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

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_compts_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['29','59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['4','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hxuencl2jZ
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 344 iterations in 0.181s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.63  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.46/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.63  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.46/0.63  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.46/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.63  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.46/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.46/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.46/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.63  thf(t20_compts_1, conjecture,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63               ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.46/0.63                   ( v2_compts_1 @ C @ A ) ) =>
% 0.46/0.63                 ( v2_compts_1 @
% 0.46/0.63                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i]:
% 0.46/0.63        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63          ( ![B:$i]:
% 0.46/0.63            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63              ( ![C:$i]:
% 0.46/0.63                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63                  ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.46/0.63                      ( v2_compts_1 @ C @ A ) ) =>
% 0.46/0.63                    ( v2_compts_1 @
% 0.46/0.63                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t20_compts_1])).
% 0.46/0.63  thf('0', plain,
% 0.46/0.63      (~ (v2_compts_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.63          sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(redefinition_k9_subset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.63       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.63         (((k9_subset_1 @ X8 @ X6 @ X7) = (k3_xboole_0 @ X6 @ X7))
% 0.46/0.63          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.46/0.63  thf('3', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.46/0.63           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.46/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.63  thf('4', plain, (~ (v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['0', '3'])).
% 0.46/0.63  thf('5', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('6', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(fc4_tops_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v4_pre_topc @ B @ A ) & 
% 0.46/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.46/0.63         ( v4_pre_topc @ C @ A ) & 
% 0.46/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.63       ( v4_pre_topc @ ( k3_xboole_0 @ B @ C ) @ A ) ))).
% 0.46/0.63  thf('7', plain,
% 0.46/0.63      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.46/0.63          | ~ (v4_pre_topc @ X21 @ X22)
% 0.46/0.63          | ~ (l1_pre_topc @ X22)
% 0.46/0.63          | ~ (v2_pre_topc @ X22)
% 0.46/0.63          | ~ (v4_pre_topc @ X23 @ X22)
% 0.46/0.63          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.46/0.63          | (v4_pre_topc @ (k3_xboole_0 @ X21 @ X23) @ X22))),
% 0.46/0.63      inference('cnf', [status(esa)], [fc4_tops_1])).
% 0.46/0.63  thf('8', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.46/0.63          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.63          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.63  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('11', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t16_compts_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.46/0.63             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.46/0.63  thf('12', plain,
% 0.46/0.63      (![X24 : $i, X25 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.46/0.63          | (v4_pre_topc @ X24 @ X25)
% 0.46/0.63          | ~ (v2_compts_1 @ X24 @ X25)
% 0.46/0.63          | ~ (v8_pre_topc @ X25)
% 0.46/0.63          | ~ (l1_pre_topc @ X25)
% 0.46/0.63          | ~ (v2_pre_topc @ X25))),
% 0.46/0.63      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.46/0.63  thf('13', plain,
% 0.46/0.63      ((~ (v2_pre_topc @ sk_A)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | ~ (v8_pre_topc @ sk_A)
% 0.46/0.63        | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.46/0.63        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.63  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('16', plain, ((v8_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('17', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('18', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['8', '9', '10', '18'])).
% 0.46/0.63  thf('20', plain,
% 0.46/0.63      ((~ (v4_pre_topc @ sk_C @ sk_A)
% 0.46/0.63        | (v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['5', '19'])).
% 0.46/0.63  thf('21', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('22', plain,
% 0.46/0.63      (![X24 : $i, X25 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.46/0.63          | (v4_pre_topc @ X24 @ X25)
% 0.46/0.63          | ~ (v2_compts_1 @ X24 @ X25)
% 0.46/0.63          | ~ (v8_pre_topc @ X25)
% 0.46/0.63          | ~ (l1_pre_topc @ X25)
% 0.46/0.63          | ~ (v2_pre_topc @ X25))),
% 0.46/0.63      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.46/0.63  thf('23', plain,
% 0.46/0.63      ((~ (v2_pre_topc @ sk_A)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | ~ (v8_pre_topc @ sk_A)
% 0.46/0.63        | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.46/0.63        | (v4_pre_topc @ sk_C @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.63  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('26', plain, ((v8_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('27', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('28', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.46/0.63  thf('29', plain, ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['20', '28'])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(dt_k1_pre_topc, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( l1_pre_topc @ A ) & 
% 0.46/0.64         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.64       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.46/0.64         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X14 : $i, X15 : $i]:
% 0.46/0.64         (~ (l1_pre_topc @ X14)
% 0.46/0.64          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.46/0.64          | (m1_pre_topc @ (k1_pre_topc @ X14 @ X15) @ X14))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.46/0.64        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.64  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('34', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['32', '33'])).
% 0.46/0.64  thf(t48_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X4 : $i, X5 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.46/0.64           = (k3_xboole_0 @ X4 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.64  thf(t36_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.46/0.64      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.46/0.64      inference('sup+', [status(thm)], ['35', '36'])).
% 0.46/0.64  thf(t3_subset, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X11 : $i, X13 : $i]:
% 0.46/0.64         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.64  thf(t39_pre_topc, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( l1_pre_topc @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.46/0.64               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.64         (~ (m1_pre_topc @ X18 @ X19)
% 0.46/0.64          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.46/0.64          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.46/0.64          | ~ (l1_pre_topc @ X19))),
% 0.46/0.64      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (l1_pre_topc @ X2)
% 0.46/0.64          | (m1_subset_1 @ (k3_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ 
% 0.46/0.64             (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.46/0.64          | ~ (m1_pre_topc @ X0 @ X2))),
% 0.46/0.64      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((m1_subset_1 @ 
% 0.46/0.64           (k3_xboole_0 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ X0) @ 
% 0.46/0.64           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.64          | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['34', '41'])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t29_pre_topc, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( l1_pre_topc @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.64           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (![X16 : $i, X17 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.46/0.64          | ((u1_struct_0 @ (k1_pre_topc @ X17 @ X16)) = (X16))
% 0.46/0.64          | ~ (l1_pre_topc @ X17))),
% 0.46/0.64      inference('cnf', [status(esa)], [t29_pre_topc])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.64        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.64  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('47', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['45', '46'])).
% 0.46/0.64  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('49', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.46/0.64          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['42', '47', '48'])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t18_compts_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.64               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.46/0.64                   ( v4_pre_topc @ C @ A ) ) =>
% 0.46/0.64                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.64          | ~ (v2_compts_1 @ X26 @ X27)
% 0.46/0.64          | ~ (r1_tarski @ X28 @ X26)
% 0.46/0.64          | ~ (v4_pre_topc @ X28 @ X27)
% 0.46/0.64          | (v2_compts_1 @ X28 @ X27)
% 0.46/0.64          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.64          | ~ (l1_pre_topc @ X27)
% 0.46/0.64          | ~ (v2_pre_topc @ X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [t18_compts_1])).
% 0.46/0.64  thf('52', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v2_pre_topc @ sk_A)
% 0.46/0.64          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.64          | (v2_compts_1 @ X0 @ sk_A)
% 0.46/0.64          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.46/0.64          | ~ (r1_tarski @ X0 @ sk_B)
% 0.46/0.64          | ~ (v2_compts_1 @ sk_B @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.46/0.64  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('55', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('56', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.64          | (v2_compts_1 @ X0 @ sk_A)
% 0.46/0.64          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.46/0.64          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.46/0.64  thf('57', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)
% 0.46/0.64          | ~ (v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.46/0.64          | (v2_compts_1 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['49', '56'])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.46/0.64      inference('sup+', [status(thm)], ['35', '36'])).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.46/0.64          | (v2_compts_1 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['57', '58'])).
% 0.46/0.64  thf('60', plain, ((v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.46/0.64      inference('sup-', [status(thm)], ['29', '59'])).
% 0.46/0.64  thf('61', plain, ($false), inference('demod', [status(thm)], ['4', '60'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

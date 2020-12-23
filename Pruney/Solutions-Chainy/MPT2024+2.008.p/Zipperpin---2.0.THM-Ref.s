%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RunEGhKqdE

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:27 EST 2020

% Result     : Theorem 16.03s
% Output     : Refutation 16.03s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 607 expanded)
%              Number of leaves         :   36 ( 188 expanded)
%              Depth                    :   19
%              Number of atoms          : 1261 (10590 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_yellow_6_type,type,(
    k9_yellow_6: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t23_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
                 => ( m1_subset_1 @ ( k2_xboole_0 @ C @ D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
                   => ( m1_subset_1 @ ( k2_xboole_0 @ C @ D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_waybel_9])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
             => ( m1_connsp_2 @ C @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ X44 ) )
      | ( m1_connsp_2 @ X45 @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X45 @ ( u1_struct_0 @ ( k9_yellow_6 @ X44 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 )
      | ( v2_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t21_waybel_9])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X34 ) )
      | ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( m1_connsp_2 @ X36 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf(t6_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( m1_connsp_2 @ B @ A @ C )
               => ( r2_hidden @ C @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( m1_connsp_2 @ X37 @ X38 @ X39 )
      | ( r2_hidden @ X39 @ X37 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X38 ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_B_1 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','24'])).

thf('26',plain,(
    m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['8','9'])).

thf('27',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r2_hidden @ sk_B_1 @ sk_C ),
    inference(clc,[status(thm)],['27','28'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ X9 )
        = X9 )
      | ~ ( r2_hidden @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('31',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('35',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ ( k2_tarski @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B_1 @ ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ X44 ) )
      | ( m1_connsp_2 @ X45 @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X45 @ ( u1_struct_0 @ ( k9_yellow_6 @ X44 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 )
      | ( v2_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t21_waybel_9])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_connsp_2 @ sk_D @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ sk_D @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_connsp_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('52',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X21 @ X20 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('57',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k4_subset_1 @ X24 @ X23 @ X25 )
        = ( k2_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k2_xboole_0 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','59'])).

thf(t39_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
              <=> ( ( r2_hidden @ B @ C )
                  & ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X41 ) )
      | ~ ( r2_hidden @ X40 @ X42 )
      | ~ ( v3_pre_topc @ X42 @ X41 )
      | ( r2_hidden @ X42 @ ( u1_struct_0 @ ( k9_yellow_6 @ X41 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('67',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('68',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X41 ) )
      | ~ ( r2_hidden @ X42 @ ( u1_struct_0 @ ( k9_yellow_6 @ X41 @ X40 ) ) )
      | ( v3_pre_topc @ X42 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X19 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('81',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf(fc7_tops_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v3_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( v3_pre_topc @ C @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ) )).

thf('84',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v3_pre_topc @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( v3_pre_topc @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v3_pre_topc @ ( k2_xboole_0 @ X31 @ X33 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc7_tops_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','88'])).

thf('90',plain,
    ( ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_D @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['65','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('93',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X41 ) )
      | ~ ( r2_hidden @ X42 @ ( u1_struct_0 @ ( k9_yellow_6 @ X41 @ X40 ) ) )
      | ( v3_pre_topc @ X42 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t39_yellow_6])).

thf('95',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_D @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['95','96','97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('101',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('105',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D ) @ sk_A ) ),
    inference(clc,[status(thm)],['90','105'])).

thf('107',plain,(
    r2_hidden @ sk_B_1 @ sk_C ),
    inference(clc,[status(thm)],['27','28'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('109',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v3_pre_topc @ ( k2_xboole_0 @ sk_C @ sk_D ) @ sk_A ),
    inference(clc,[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ sk_D ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','110'])).

thf('112',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    r2_hidden @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('117',plain,(
    ! [X26: $i,X27: $i] :
      ( ( m1_subset_1 @ X26 @ X27 )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('118',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    $false ),
    inference(demod,[status(thm)],['0','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RunEGhKqdE
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:59:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 16.03/16.22  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 16.03/16.22  % Solved by: fo/fo7.sh
% 16.03/16.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 16.03/16.22  % done 21267 iterations in 15.758s
% 16.03/16.22  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 16.03/16.22  % SZS output start Refutation
% 16.03/16.22  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 16.03/16.22  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 16.03/16.22  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 16.03/16.22  thf(sk_A_type, type, sk_A: $i).
% 16.03/16.22  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 16.03/16.22  thf(k9_yellow_6_type, type, k9_yellow_6: $i > $i > $i).
% 16.03/16.22  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 16.03/16.22  thf(sk_D_type, type, sk_D: $i).
% 16.03/16.22  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 16.03/16.22  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 16.03/16.22  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 16.03/16.22  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 16.03/16.22  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 16.03/16.22  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 16.03/16.22  thf(sk_B_1_type, type, sk_B_1: $i).
% 16.03/16.22  thf(sk_C_type, type, sk_C: $i).
% 16.03/16.22  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 16.03/16.22  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 16.03/16.22  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 16.03/16.22  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 16.03/16.22  thf(t23_waybel_9, conjecture,
% 16.03/16.22    (![A:$i]:
% 16.03/16.22     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 16.03/16.22       ( ![B:$i]:
% 16.03/16.22         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 16.03/16.22           ( ![C:$i]:
% 16.03/16.22             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 16.03/16.22               ( ![D:$i]:
% 16.03/16.22                 ( ( m1_subset_1 @
% 16.03/16.22                     D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 16.03/16.22                   ( m1_subset_1 @
% 16.03/16.22                     ( k2_xboole_0 @ C @ D ) @ 
% 16.03/16.22                     ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 16.03/16.22  thf(zf_stmt_0, negated_conjecture,
% 16.03/16.22    (~( ![A:$i]:
% 16.03/16.22        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 16.03/16.22            ( l1_pre_topc @ A ) ) =>
% 16.03/16.22          ( ![B:$i]:
% 16.03/16.22            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 16.03/16.22              ( ![C:$i]:
% 16.03/16.22                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 16.03/16.22                  ( ![D:$i]:
% 16.03/16.22                    ( ( m1_subset_1 @
% 16.03/16.22                        D @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 16.03/16.22                      ( m1_subset_1 @
% 16.03/16.22                        ( k2_xboole_0 @ C @ D ) @ 
% 16.03/16.22                        ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 16.03/16.22    inference('cnf.neg', [status(esa)], [t23_waybel_9])).
% 16.03/16.22  thf('0', plain,
% 16.03/16.22      (~ (m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 16.03/16.22          (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('2', plain,
% 16.03/16.22      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf(t21_waybel_9, axiom,
% 16.03/16.22    (![A:$i]:
% 16.03/16.22     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 16.03/16.22       ( ![B:$i]:
% 16.03/16.22         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 16.03/16.22           ( ![C:$i]:
% 16.03/16.22             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 16.03/16.22               ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ))).
% 16.03/16.22  thf('3', plain,
% 16.03/16.22      (![X43 : $i, X44 : $i, X45 : $i]:
% 16.03/16.22         (~ (m1_subset_1 @ X43 @ (u1_struct_0 @ X44))
% 16.03/16.22          | (m1_connsp_2 @ X45 @ X44 @ X43)
% 16.03/16.22          | ~ (m1_subset_1 @ X45 @ (u1_struct_0 @ (k9_yellow_6 @ X44 @ X43)))
% 16.03/16.22          | ~ (l1_pre_topc @ X44)
% 16.03/16.22          | ~ (v2_pre_topc @ X44)
% 16.03/16.22          | (v2_struct_0 @ X44))),
% 16.03/16.22      inference('cnf', [status(esa)], [t21_waybel_9])).
% 16.03/16.22  thf('4', plain,
% 16.03/16.22      (((v2_struct_0 @ sk_A)
% 16.03/16.22        | ~ (v2_pre_topc @ sk_A)
% 16.03/16.22        | ~ (l1_pre_topc @ sk_A)
% 16.03/16.22        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)
% 16.03/16.22        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 16.03/16.22      inference('sup-', [status(thm)], ['2', '3'])).
% 16.03/16.22  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('8', plain,
% 16.03/16.22      (((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1))),
% 16.03/16.22      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 16.03/16.22  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('10', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)),
% 16.03/16.22      inference('clc', [status(thm)], ['8', '9'])).
% 16.03/16.22  thf('11', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf(dt_m1_connsp_2, axiom,
% 16.03/16.22    (![A:$i,B:$i]:
% 16.03/16.22     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 16.03/16.22         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 16.03/16.22       ( ![C:$i]:
% 16.03/16.22         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 16.03/16.22           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 16.03/16.22  thf('12', plain,
% 16.03/16.22      (![X34 : $i, X35 : $i, X36 : $i]:
% 16.03/16.22         (~ (l1_pre_topc @ X34)
% 16.03/16.22          | ~ (v2_pre_topc @ X34)
% 16.03/16.22          | (v2_struct_0 @ X34)
% 16.03/16.22          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X34))
% 16.03/16.22          | (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 16.03/16.22          | ~ (m1_connsp_2 @ X36 @ X34 @ X35))),
% 16.03/16.22      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 16.03/16.22  thf('13', plain,
% 16.03/16.22      (![X0 : $i]:
% 16.03/16.22         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 16.03/16.22          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.03/16.22          | (v2_struct_0 @ sk_A)
% 16.03/16.22          | ~ (v2_pre_topc @ sk_A)
% 16.03/16.22          | ~ (l1_pre_topc @ sk_A))),
% 16.03/16.22      inference('sup-', [status(thm)], ['11', '12'])).
% 16.03/16.22  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('16', plain,
% 16.03/16.22      (![X0 : $i]:
% 16.03/16.22         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1)
% 16.03/16.22          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.03/16.22          | (v2_struct_0 @ sk_A))),
% 16.03/16.22      inference('demod', [status(thm)], ['13', '14', '15'])).
% 16.03/16.22  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('18', plain,
% 16.03/16.22      (![X0 : $i]:
% 16.03/16.22         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.03/16.22          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1))),
% 16.03/16.22      inference('clc', [status(thm)], ['16', '17'])).
% 16.03/16.22  thf('19', plain,
% 16.03/16.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.03/16.22      inference('sup-', [status(thm)], ['10', '18'])).
% 16.03/16.22  thf(t6_connsp_2, axiom,
% 16.03/16.22    (![A:$i]:
% 16.03/16.22     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 16.03/16.22       ( ![B:$i]:
% 16.03/16.22         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 16.03/16.22           ( ![C:$i]:
% 16.03/16.22             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 16.03/16.22               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 16.03/16.22  thf('20', plain,
% 16.03/16.22      (![X37 : $i, X38 : $i, X39 : $i]:
% 16.03/16.22         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 16.03/16.22          | ~ (m1_connsp_2 @ X37 @ X38 @ X39)
% 16.03/16.22          | (r2_hidden @ X39 @ X37)
% 16.03/16.22          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X38))
% 16.03/16.22          | ~ (l1_pre_topc @ X38)
% 16.03/16.22          | ~ (v2_pre_topc @ X38)
% 16.03/16.22          | (v2_struct_0 @ X38))),
% 16.03/16.22      inference('cnf', [status(esa)], [t6_connsp_2])).
% 16.03/16.22  thf('21', plain,
% 16.03/16.22      (![X0 : $i]:
% 16.03/16.22         ((v2_struct_0 @ sk_A)
% 16.03/16.22          | ~ (v2_pre_topc @ sk_A)
% 16.03/16.22          | ~ (l1_pre_topc @ sk_A)
% 16.03/16.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 16.03/16.22          | (r2_hidden @ X0 @ sk_C)
% 16.03/16.22          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0))),
% 16.03/16.22      inference('sup-', [status(thm)], ['19', '20'])).
% 16.03/16.22  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('24', plain,
% 16.03/16.22      (![X0 : $i]:
% 16.03/16.22         ((v2_struct_0 @ sk_A)
% 16.03/16.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 16.03/16.22          | (r2_hidden @ X0 @ sk_C)
% 16.03/16.22          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0))),
% 16.03/16.22      inference('demod', [status(thm)], ['21', '22', '23'])).
% 16.03/16.22  thf('25', plain,
% 16.03/16.22      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)
% 16.03/16.22        | (r2_hidden @ sk_B_1 @ sk_C)
% 16.03/16.22        | (v2_struct_0 @ sk_A))),
% 16.03/16.22      inference('sup-', [status(thm)], ['1', '24'])).
% 16.03/16.22  thf('26', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)),
% 16.03/16.22      inference('clc', [status(thm)], ['8', '9'])).
% 16.03/16.22  thf('27', plain, (((r2_hidden @ sk_B_1 @ sk_C) | (v2_struct_0 @ sk_A))),
% 16.03/16.22      inference('demod', [status(thm)], ['25', '26'])).
% 16.03/16.22  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('29', plain, ((r2_hidden @ sk_B_1 @ sk_C)),
% 16.03/16.22      inference('clc', [status(thm)], ['27', '28'])).
% 16.03/16.22  thf(l22_zfmisc_1, axiom,
% 16.03/16.22    (![A:$i,B:$i]:
% 16.03/16.22     ( ( r2_hidden @ A @ B ) =>
% 16.03/16.22       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 16.03/16.22  thf('30', plain,
% 16.03/16.22      (![X9 : $i, X10 : $i]:
% 16.03/16.22         (((k2_xboole_0 @ (k1_tarski @ X10) @ X9) = (X9))
% 16.03/16.22          | ~ (r2_hidden @ X10 @ X9))),
% 16.03/16.22      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 16.03/16.22  thf('31', plain, (((k2_xboole_0 @ (k1_tarski @ sk_B_1) @ sk_C) = (sk_C))),
% 16.03/16.22      inference('sup-', [status(thm)], ['29', '30'])).
% 16.03/16.22  thf(t7_xboole_1, axiom,
% 16.03/16.22    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 16.03/16.22  thf('32', plain,
% 16.03/16.22      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 16.03/16.22      inference('cnf', [status(esa)], [t7_xboole_1])).
% 16.03/16.22  thf(t11_xboole_1, axiom,
% 16.03/16.22    (![A:$i,B:$i,C:$i]:
% 16.03/16.22     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 16.03/16.22  thf('33', plain,
% 16.03/16.22      (![X3 : $i, X4 : $i, X5 : $i]:
% 16.03/16.22         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 16.03/16.22      inference('cnf', [status(esa)], [t11_xboole_1])).
% 16.03/16.22  thf('34', plain,
% 16.03/16.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.03/16.22         (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 16.03/16.22      inference('sup-', [status(thm)], ['32', '33'])).
% 16.03/16.22  thf(t69_enumset1, axiom,
% 16.03/16.22    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 16.03/16.22  thf('35', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 16.03/16.22      inference('cnf', [status(esa)], [t69_enumset1])).
% 16.03/16.22  thf(t38_zfmisc_1, axiom,
% 16.03/16.22    (![A:$i,B:$i,C:$i]:
% 16.03/16.22     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 16.03/16.22       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 16.03/16.22  thf('36', plain,
% 16.03/16.22      (![X13 : $i, X14 : $i, X15 : $i]:
% 16.03/16.22         ((r2_hidden @ X13 @ X14)
% 16.03/16.22          | ~ (r1_tarski @ (k2_tarski @ X13 @ X15) @ X14))),
% 16.03/16.22      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 16.03/16.22  thf('37', plain,
% 16.03/16.22      (![X0 : $i, X1 : $i]:
% 16.03/16.22         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 16.03/16.22      inference('sup-', [status(thm)], ['35', '36'])).
% 16.03/16.22  thf('38', plain,
% 16.03/16.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.03/16.22         (r2_hidden @ X2 @ 
% 16.03/16.22          (k2_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X2) @ X1) @ X0))),
% 16.03/16.22      inference('sup-', [status(thm)], ['34', '37'])).
% 16.03/16.22  thf('39', plain,
% 16.03/16.22      (![X0 : $i]: (r2_hidden @ sk_B_1 @ (k2_xboole_0 @ sk_C @ X0))),
% 16.03/16.22      inference('sup+', [status(thm)], ['31', '38'])).
% 16.03/16.22  thf('40', plain,
% 16.03/16.22      ((m1_subset_1 @ sk_D @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('41', plain,
% 16.03/16.22      (![X43 : $i, X44 : $i, X45 : $i]:
% 16.03/16.22         (~ (m1_subset_1 @ X43 @ (u1_struct_0 @ X44))
% 16.03/16.22          | (m1_connsp_2 @ X45 @ X44 @ X43)
% 16.03/16.22          | ~ (m1_subset_1 @ X45 @ (u1_struct_0 @ (k9_yellow_6 @ X44 @ X43)))
% 16.03/16.22          | ~ (l1_pre_topc @ X44)
% 16.03/16.22          | ~ (v2_pre_topc @ X44)
% 16.03/16.22          | (v2_struct_0 @ X44))),
% 16.03/16.22      inference('cnf', [status(esa)], [t21_waybel_9])).
% 16.03/16.22  thf('42', plain,
% 16.03/16.22      (((v2_struct_0 @ sk_A)
% 16.03/16.22        | ~ (v2_pre_topc @ sk_A)
% 16.03/16.22        | ~ (l1_pre_topc @ sk_A)
% 16.03/16.22        | (m1_connsp_2 @ sk_D @ sk_A @ sk_B_1)
% 16.03/16.22        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 16.03/16.22      inference('sup-', [status(thm)], ['40', '41'])).
% 16.03/16.22  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('45', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('46', plain,
% 16.03/16.22      (((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_D @ sk_A @ sk_B_1))),
% 16.03/16.22      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 16.03/16.22  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('48', plain, ((m1_connsp_2 @ sk_D @ sk_A @ sk_B_1)),
% 16.03/16.22      inference('clc', [status(thm)], ['46', '47'])).
% 16.03/16.22  thf('49', plain,
% 16.03/16.22      (![X0 : $i]:
% 16.03/16.22         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.03/16.22          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B_1))),
% 16.03/16.22      inference('clc', [status(thm)], ['16', '17'])).
% 16.03/16.22  thf('50', plain,
% 16.03/16.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.03/16.22      inference('sup-', [status(thm)], ['48', '49'])).
% 16.03/16.22  thf('51', plain,
% 16.03/16.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.03/16.22      inference('sup-', [status(thm)], ['10', '18'])).
% 16.03/16.22  thf(dt_k4_subset_1, axiom,
% 16.03/16.22    (![A:$i,B:$i,C:$i]:
% 16.03/16.22     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 16.03/16.22         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 16.03/16.22       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 16.03/16.22  thf('52', plain,
% 16.03/16.22      (![X20 : $i, X21 : $i, X22 : $i]:
% 16.03/16.22         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 16.03/16.22          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21))
% 16.03/16.22          | (m1_subset_1 @ (k4_subset_1 @ X21 @ X20 @ X22) @ 
% 16.03/16.22             (k1_zfmisc_1 @ X21)))),
% 16.03/16.22      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 16.03/16.22  thf('53', plain,
% 16.03/16.22      (![X0 : $i]:
% 16.03/16.22         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 16.03/16.22           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.03/16.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 16.03/16.22      inference('sup-', [status(thm)], ['51', '52'])).
% 16.03/16.22  thf('54', plain,
% 16.03/16.22      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D) @ 
% 16.03/16.22        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.03/16.22      inference('sup-', [status(thm)], ['50', '53'])).
% 16.03/16.22  thf('55', plain,
% 16.03/16.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.03/16.22      inference('sup-', [status(thm)], ['48', '49'])).
% 16.03/16.22  thf('56', plain,
% 16.03/16.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.03/16.22      inference('sup-', [status(thm)], ['10', '18'])).
% 16.03/16.22  thf(redefinition_k4_subset_1, axiom,
% 16.03/16.22    (![A:$i,B:$i,C:$i]:
% 16.03/16.22     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 16.03/16.22         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 16.03/16.22       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 16.03/16.22  thf('57', plain,
% 16.03/16.22      (![X23 : $i, X24 : $i, X25 : $i]:
% 16.03/16.22         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 16.03/16.22          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24))
% 16.03/16.22          | ((k4_subset_1 @ X24 @ X23 @ X25) = (k2_xboole_0 @ X23 @ X25)))),
% 16.03/16.22      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 16.03/16.22  thf('58', plain,
% 16.03/16.22      (![X0 : $i]:
% 16.03/16.22         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 16.03/16.22            = (k2_xboole_0 @ sk_C @ X0))
% 16.03/16.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 16.03/16.22      inference('sup-', [status(thm)], ['56', '57'])).
% 16.03/16.22  thf('59', plain,
% 16.03/16.22      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D)
% 16.03/16.22         = (k2_xboole_0 @ sk_C @ sk_D))),
% 16.03/16.22      inference('sup-', [status(thm)], ['55', '58'])).
% 16.03/16.22  thf('60', plain,
% 16.03/16.22      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 16.03/16.22        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.03/16.22      inference('demod', [status(thm)], ['54', '59'])).
% 16.03/16.22  thf(t39_yellow_6, axiom,
% 16.03/16.22    (![A:$i]:
% 16.03/16.22     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 16.03/16.22       ( ![B:$i]:
% 16.03/16.22         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 16.03/16.22           ( ![C:$i]:
% 16.03/16.22             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 16.03/16.22               ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) <=>
% 16.03/16.22                 ( ( r2_hidden @ B @ C ) & ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 16.03/16.22  thf('61', plain,
% 16.03/16.22      (![X40 : $i, X41 : $i, X42 : $i]:
% 16.03/16.22         (~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X41))
% 16.03/16.22          | ~ (r2_hidden @ X40 @ X42)
% 16.03/16.22          | ~ (v3_pre_topc @ X42 @ X41)
% 16.03/16.22          | (r2_hidden @ X42 @ (u1_struct_0 @ (k9_yellow_6 @ X41 @ X40)))
% 16.03/16.22          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 16.03/16.22          | ~ (l1_pre_topc @ X41)
% 16.03/16.22          | ~ (v2_pre_topc @ X41)
% 16.03/16.22          | (v2_struct_0 @ X41))),
% 16.03/16.22      inference('cnf', [status(esa)], [t39_yellow_6])).
% 16.03/16.22  thf('62', plain,
% 16.03/16.22      (![X0 : $i]:
% 16.03/16.22         ((v2_struct_0 @ sk_A)
% 16.03/16.22          | ~ (v2_pre_topc @ sk_A)
% 16.03/16.22          | ~ (l1_pre_topc @ sk_A)
% 16.03/16.22          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 16.03/16.22             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 16.03/16.22          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D) @ sk_A)
% 16.03/16.22          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D))
% 16.03/16.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 16.03/16.22      inference('sup-', [status(thm)], ['60', '61'])).
% 16.03/16.22  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('65', plain,
% 16.03/16.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.03/16.22      inference('sup-', [status(thm)], ['48', '49'])).
% 16.03/16.22  thf('66', plain,
% 16.03/16.22      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf(d2_subset_1, axiom,
% 16.03/16.22    (![A:$i,B:$i]:
% 16.03/16.22     ( ( ( v1_xboole_0 @ A ) =>
% 16.03/16.22         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 16.03/16.22       ( ( ~( v1_xboole_0 @ A ) ) =>
% 16.03/16.22         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 16.03/16.22  thf('67', plain,
% 16.03/16.22      (![X17 : $i, X18 : $i]:
% 16.03/16.22         (~ (m1_subset_1 @ X17 @ X18)
% 16.03/16.22          | (r2_hidden @ X17 @ X18)
% 16.03/16.22          | (v1_xboole_0 @ X18))),
% 16.03/16.22      inference('cnf', [status(esa)], [d2_subset_1])).
% 16.03/16.22  thf('68', plain,
% 16.03/16.22      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 16.03/16.22        | (r2_hidden @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 16.03/16.22      inference('sup-', [status(thm)], ['66', '67'])).
% 16.03/16.22  thf('69', plain,
% 16.03/16.22      (![X40 : $i, X41 : $i, X42 : $i]:
% 16.03/16.22         (~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X41))
% 16.03/16.22          | ~ (r2_hidden @ X42 @ (u1_struct_0 @ (k9_yellow_6 @ X41 @ X40)))
% 16.03/16.22          | (v3_pre_topc @ X42 @ X41)
% 16.03/16.22          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 16.03/16.22          | ~ (l1_pre_topc @ X41)
% 16.03/16.22          | ~ (v2_pre_topc @ X41)
% 16.03/16.22          | (v2_struct_0 @ X41))),
% 16.03/16.22      inference('cnf', [status(esa)], [t39_yellow_6])).
% 16.03/16.22  thf('70', plain,
% 16.03/16.22      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 16.03/16.22        | (v2_struct_0 @ sk_A)
% 16.03/16.22        | ~ (v2_pre_topc @ sk_A)
% 16.03/16.22        | ~ (l1_pre_topc @ sk_A)
% 16.03/16.22        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.03/16.22        | (v3_pre_topc @ sk_C @ sk_A)
% 16.03/16.22        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 16.03/16.22      inference('sup-', [status(thm)], ['68', '69'])).
% 16.03/16.22  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('73', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('74', plain,
% 16.03/16.22      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 16.03/16.22        | (v2_struct_0 @ sk_A)
% 16.03/16.22        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.03/16.22        | (v3_pre_topc @ sk_C @ sk_A))),
% 16.03/16.22      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 16.03/16.22  thf('75', plain,
% 16.03/16.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.03/16.22      inference('sup-', [status(thm)], ['10', '18'])).
% 16.03/16.22  thf('76', plain,
% 16.03/16.22      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 16.03/16.22        | (v2_struct_0 @ sk_A)
% 16.03/16.22        | (v3_pre_topc @ sk_C @ sk_A))),
% 16.03/16.22      inference('demod', [status(thm)], ['74', '75'])).
% 16.03/16.22  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('78', plain,
% 16.03/16.22      (((v3_pre_topc @ sk_C @ sk_A)
% 16.03/16.22        | (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 16.03/16.22      inference('clc', [status(thm)], ['76', '77'])).
% 16.03/16.22  thf('79', plain,
% 16.03/16.22      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('80', plain,
% 16.03/16.22      (![X18 : $i, X19 : $i]:
% 16.03/16.22         (~ (m1_subset_1 @ X19 @ X18)
% 16.03/16.22          | (v1_xboole_0 @ X19)
% 16.03/16.22          | ~ (v1_xboole_0 @ X18))),
% 16.03/16.22      inference('cnf', [status(esa)], [d2_subset_1])).
% 16.03/16.22  thf('81', plain,
% 16.03/16.22      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 16.03/16.22        | (v1_xboole_0 @ sk_C))),
% 16.03/16.22      inference('sup-', [status(thm)], ['79', '80'])).
% 16.03/16.22  thf('82', plain, (((v3_pre_topc @ sk_C @ sk_A) | (v1_xboole_0 @ sk_C))),
% 16.03/16.22      inference('sup-', [status(thm)], ['78', '81'])).
% 16.03/16.22  thf('83', plain,
% 16.03/16.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.03/16.22      inference('sup-', [status(thm)], ['10', '18'])).
% 16.03/16.22  thf(fc7_tops_1, axiom,
% 16.03/16.22    (![A:$i,B:$i,C:$i]:
% 16.03/16.22     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v3_pre_topc @ B @ A ) & 
% 16.03/16.22         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 16.03/16.22         ( v3_pre_topc @ C @ A ) & 
% 16.03/16.22         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 16.03/16.22       ( v3_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ))).
% 16.03/16.22  thf('84', plain,
% 16.03/16.22      (![X31 : $i, X32 : $i, X33 : $i]:
% 16.03/16.22         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 16.03/16.22          | ~ (v3_pre_topc @ X31 @ X32)
% 16.03/16.22          | ~ (l1_pre_topc @ X32)
% 16.03/16.22          | ~ (v2_pre_topc @ X32)
% 16.03/16.22          | ~ (v3_pre_topc @ X33 @ X32)
% 16.03/16.22          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 16.03/16.22          | (v3_pre_topc @ (k2_xboole_0 @ X31 @ X33) @ X32))),
% 16.03/16.22      inference('cnf', [status(esa)], [fc7_tops_1])).
% 16.03/16.22  thf('85', plain,
% 16.03/16.22      (![X0 : $i]:
% 16.03/16.22         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 16.03/16.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.03/16.22          | ~ (v3_pre_topc @ X0 @ sk_A)
% 16.03/16.22          | ~ (v2_pre_topc @ sk_A)
% 16.03/16.22          | ~ (l1_pre_topc @ sk_A)
% 16.03/16.22          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 16.03/16.22      inference('sup-', [status(thm)], ['83', '84'])).
% 16.03/16.22  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('88', plain,
% 16.03/16.22      (![X0 : $i]:
% 16.03/16.22         ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A)
% 16.03/16.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.03/16.22          | ~ (v3_pre_topc @ X0 @ sk_A)
% 16.03/16.22          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 16.03/16.22      inference('demod', [status(thm)], ['85', '86', '87'])).
% 16.03/16.22  thf('89', plain,
% 16.03/16.22      (![X0 : $i]:
% 16.03/16.22         ((v1_xboole_0 @ sk_C)
% 16.03/16.22          | ~ (v3_pre_topc @ X0 @ sk_A)
% 16.03/16.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.03/16.22          | (v3_pre_topc @ (k2_xboole_0 @ sk_C @ X0) @ sk_A))),
% 16.03/16.22      inference('sup-', [status(thm)], ['82', '88'])).
% 16.03/16.22  thf('90', plain,
% 16.03/16.22      (((v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D) @ sk_A)
% 16.03/16.22        | ~ (v3_pre_topc @ sk_D @ sk_A)
% 16.03/16.22        | (v1_xboole_0 @ sk_C))),
% 16.03/16.22      inference('sup-', [status(thm)], ['65', '89'])).
% 16.03/16.22  thf('91', plain,
% 16.03/16.22      ((m1_subset_1 @ sk_D @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('92', plain,
% 16.03/16.22      (![X17 : $i, X18 : $i]:
% 16.03/16.22         (~ (m1_subset_1 @ X17 @ X18)
% 16.03/16.22          | (r2_hidden @ X17 @ X18)
% 16.03/16.22          | (v1_xboole_0 @ X18))),
% 16.03/16.22      inference('cnf', [status(esa)], [d2_subset_1])).
% 16.03/16.22  thf('93', plain,
% 16.03/16.22      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 16.03/16.22        | (r2_hidden @ sk_D @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 16.03/16.22      inference('sup-', [status(thm)], ['91', '92'])).
% 16.03/16.22  thf('94', plain,
% 16.03/16.22      (![X40 : $i, X41 : $i, X42 : $i]:
% 16.03/16.22         (~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X41))
% 16.03/16.22          | ~ (r2_hidden @ X42 @ (u1_struct_0 @ (k9_yellow_6 @ X41 @ X40)))
% 16.03/16.22          | (v3_pre_topc @ X42 @ X41)
% 16.03/16.22          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 16.03/16.22          | ~ (l1_pre_topc @ X41)
% 16.03/16.22          | ~ (v2_pre_topc @ X41)
% 16.03/16.22          | (v2_struct_0 @ X41))),
% 16.03/16.22      inference('cnf', [status(esa)], [t39_yellow_6])).
% 16.03/16.22  thf('95', plain,
% 16.03/16.22      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 16.03/16.22        | (v2_struct_0 @ sk_A)
% 16.03/16.22        | ~ (v2_pre_topc @ sk_A)
% 16.03/16.22        | ~ (l1_pre_topc @ sk_A)
% 16.03/16.22        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.03/16.22        | (v3_pre_topc @ sk_D @ sk_A)
% 16.03/16.22        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 16.03/16.22      inference('sup-', [status(thm)], ['93', '94'])).
% 16.03/16.22  thf('96', plain, ((v2_pre_topc @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('98', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('99', plain,
% 16.03/16.22      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 16.03/16.22        | (v2_struct_0 @ sk_A)
% 16.03/16.22        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.03/16.22        | (v3_pre_topc @ sk_D @ sk_A))),
% 16.03/16.22      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 16.03/16.22  thf('100', plain,
% 16.03/16.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.03/16.22      inference('sup-', [status(thm)], ['48', '49'])).
% 16.03/16.22  thf('101', plain,
% 16.03/16.22      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 16.03/16.22        | (v2_struct_0 @ sk_A)
% 16.03/16.22        | (v3_pre_topc @ sk_D @ sk_A))),
% 16.03/16.22      inference('demod', [status(thm)], ['99', '100'])).
% 16.03/16.22  thf('102', plain, (~ (v2_struct_0 @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('103', plain,
% 16.03/16.22      (((v3_pre_topc @ sk_D @ sk_A)
% 16.03/16.22        | (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1))))),
% 16.03/16.22      inference('clc', [status(thm)], ['101', '102'])).
% 16.03/16.22  thf('104', plain,
% 16.03/16.22      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 16.03/16.22        | (v1_xboole_0 @ sk_C))),
% 16.03/16.22      inference('sup-', [status(thm)], ['79', '80'])).
% 16.03/16.22  thf('105', plain, (((v3_pre_topc @ sk_D @ sk_A) | (v1_xboole_0 @ sk_C))),
% 16.03/16.22      inference('sup-', [status(thm)], ['103', '104'])).
% 16.03/16.22  thf('106', plain,
% 16.03/16.22      (((v1_xboole_0 @ sk_C)
% 16.03/16.22        | (v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D) @ sk_A))),
% 16.03/16.22      inference('clc', [status(thm)], ['90', '105'])).
% 16.03/16.22  thf('107', plain, ((r2_hidden @ sk_B_1 @ sk_C)),
% 16.03/16.22      inference('clc', [status(thm)], ['27', '28'])).
% 16.03/16.22  thf(d1_xboole_0, axiom,
% 16.03/16.22    (![A:$i]:
% 16.03/16.22     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 16.03/16.22  thf('108', plain,
% 16.03/16.22      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 16.03/16.22      inference('cnf', [status(esa)], [d1_xboole_0])).
% 16.03/16.22  thf('109', plain, (~ (v1_xboole_0 @ sk_C)),
% 16.03/16.22      inference('sup-', [status(thm)], ['107', '108'])).
% 16.03/16.22  thf('110', plain, ((v3_pre_topc @ (k2_xboole_0 @ sk_C @ sk_D) @ sk_A)),
% 16.03/16.22      inference('clc', [status(thm)], ['106', '109'])).
% 16.03/16.22  thf('111', plain,
% 16.03/16.22      (![X0 : $i]:
% 16.03/16.22         ((v2_struct_0 @ sk_A)
% 16.03/16.22          | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 16.03/16.22             (u1_struct_0 @ (k9_yellow_6 @ sk_A @ X0)))
% 16.03/16.22          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ sk_D))
% 16.03/16.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 16.03/16.22      inference('demod', [status(thm)], ['62', '63', '64', '110'])).
% 16.03/16.22  thf('112', plain,
% 16.03/16.22      ((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 16.03/16.22        | (r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 16.03/16.22           (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 16.03/16.22        | (v2_struct_0 @ sk_A))),
% 16.03/16.22      inference('sup-', [status(thm)], ['39', '111'])).
% 16.03/16.22  thf('113', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('114', plain,
% 16.03/16.22      (((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 16.03/16.22         (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))
% 16.03/16.22        | (v2_struct_0 @ sk_A))),
% 16.03/16.22      inference('demod', [status(thm)], ['112', '113'])).
% 16.03/16.22  thf('115', plain, (~ (v2_struct_0 @ sk_A)),
% 16.03/16.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.03/16.22  thf('116', plain,
% 16.03/16.22      ((r2_hidden @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 16.03/16.22        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 16.03/16.22      inference('clc', [status(thm)], ['114', '115'])).
% 16.03/16.22  thf(t1_subset, axiom,
% 16.03/16.22    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 16.03/16.22  thf('117', plain,
% 16.03/16.22      (![X26 : $i, X27 : $i]:
% 16.03/16.22         ((m1_subset_1 @ X26 @ X27) | ~ (r2_hidden @ X26 @ X27))),
% 16.03/16.22      inference('cnf', [status(esa)], [t1_subset])).
% 16.03/16.22  thf('118', plain,
% 16.03/16.22      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 16.03/16.22        (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B_1)))),
% 16.03/16.22      inference('sup-', [status(thm)], ['116', '117'])).
% 16.03/16.22  thf('119', plain, ($false), inference('demod', [status(thm)], ['0', '118'])).
% 16.03/16.22  
% 16.03/16.22  % SZS output end Refutation
% 16.03/16.22  
% 16.03/16.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

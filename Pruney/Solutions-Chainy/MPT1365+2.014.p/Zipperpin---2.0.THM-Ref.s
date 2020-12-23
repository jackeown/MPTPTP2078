%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xnKodu38Et

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:37 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 393 expanded)
%              Number of leaves         :   31 ( 132 expanded)
%              Depth                    :   16
%              Number of atoms          : 1045 (5049 expanded)
%              Number of equality atoms :   37 ( 135 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X6 @ X8 @ X7 )
        = ( k9_subset_1 @ X6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    = sk_C ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ sk_C @ sk_C ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X6 @ X8 @ X7 )
        = ( k9_subset_1 @ X6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_C @ X0 @ sk_C )
      = ( k9_subset_1 @ sk_C @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_C @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_C )
      = ( k9_subset_1 @ sk_C @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('29',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k9_subset_1 @ X0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_C )
      = ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C @ X0 )
      = ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['10','37'])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X17 @ X18 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('43',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('47',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ( m1_subset_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('51',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X20 @ X19 ) )
        = X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('58',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v2_compts_1 @ X29 @ X30 )
      | ~ ( r1_tarski @ X31 @ X29 )
      | ~ ( v4_pre_topc @ X31 @ X30 )
      | ( v2_compts_1 @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t18_compts_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_compts_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_C )
      | ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A )
    | ( v2_compts_1 @ ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['40','66'])).

thf('68',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('69',plain,
    ( ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A )
    | ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_compts_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('72',plain,(
    ~ ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(clc,[status(thm)],['69','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
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

thf('76',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v4_pre_topc @ X24 @ X25 )
      | ~ ( v4_pre_topc @ X26 @ X25 )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 @ X26 ) @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t35_tops_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('82',plain,(
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

thf('83',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v4_pre_topc @ X27 @ X28 )
      | ~ ( v2_compts_1 @ X27 @ X28 )
      | ~ ( v8_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('84',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['84','85','86','87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','89'])).

thf('91',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ( v4_pre_topc @ ( k3_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['74','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v4_pre_topc @ X27 @ X28 )
      | ~ ( v2_compts_1 @ X27 @ X28 )
      | ~ ( v8_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('94',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_C @ sk_A )
    | ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('101',plain,(
    v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['91','99','100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['73','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xnKodu38Et
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.83  % Solved by: fo/fo7.sh
% 0.59/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.83  % done 670 iterations in 0.378s
% 0.59/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.83  % SZS output start Refutation
% 0.59/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.83  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.59/0.83  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.59/0.83  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.83  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.59/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.83  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.59/0.83  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.59/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.83  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.59/0.83  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.59/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.83  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.59/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.83  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.59/0.83  thf(t20_compts_1, conjecture,
% 0.59/0.83    (![A:$i]:
% 0.59/0.83     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.83       ( ![B:$i]:
% 0.59/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.83           ( ![C:$i]:
% 0.59/0.83             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.83               ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.59/0.83                   ( v2_compts_1 @ C @ A ) ) =>
% 0.59/0.83                 ( v2_compts_1 @
% 0.59/0.83                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.59/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.83    (~( ![A:$i]:
% 0.59/0.83        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.83          ( ![B:$i]:
% 0.59/0.83            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.83              ( ![C:$i]:
% 0.59/0.83                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.83                  ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.59/0.83                      ( v2_compts_1 @ C @ A ) ) =>
% 0.59/0.83                    ( v2_compts_1 @
% 0.59/0.83                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.59/0.83    inference('cnf.neg', [status(esa)], [t20_compts_1])).
% 0.59/0.83  thf('0', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(commutativity_k9_subset_1, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i]:
% 0.59/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.83       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.59/0.83  thf('1', plain,
% 0.59/0.83      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.59/0.83         (((k9_subset_1 @ X6 @ X8 @ X7) = (k9_subset_1 @ X6 @ X7 @ X8))
% 0.59/0.83          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.59/0.83      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.59/0.83  thf('2', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.59/0.83           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['0', '1'])).
% 0.59/0.83  thf('3', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(redefinition_k9_subset_1, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i]:
% 0.59/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.83       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.59/0.83  thf('4', plain,
% 0.59/0.83      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.59/0.83         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.59/0.83          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.59/0.83      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.59/0.83  thf('5', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.59/0.83           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.59/0.83      inference('sup-', [status(thm)], ['3', '4'])).
% 0.59/0.83  thf('6', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((k3_xboole_0 @ X0 @ sk_B)
% 0.59/0.83           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.59/0.83      inference('demod', [status(thm)], ['2', '5'])).
% 0.59/0.83  thf('7', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('8', plain,
% 0.59/0.83      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.59/0.83         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.59/0.83          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.59/0.83      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.59/0.83  thf('9', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.59/0.83           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.59/0.83      inference('sup-', [status(thm)], ['7', '8'])).
% 0.59/0.83  thf('10', plain,
% 0.59/0.83      (((k3_xboole_0 @ sk_C @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.59/0.83      inference('sup+', [status(thm)], ['6', '9'])).
% 0.59/0.83  thf('11', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(t3_subset, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.83  thf('12', plain,
% 0.59/0.83      (![X14 : $i, X15 : $i]:
% 0.59/0.83         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.59/0.83      inference('cnf', [status(esa)], [t3_subset])).
% 0.59/0.83  thf('13', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.83  thf(t28_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.59/0.83  thf('14', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.59/0.83      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.83  thf('15', plain, (((k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A)) = (sk_C))),
% 0.59/0.83      inference('sup-', [status(thm)], ['13', '14'])).
% 0.59/0.83  thf(t48_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.83  thf('16', plain,
% 0.59/0.83      (![X4 : $i, X5 : $i]:
% 0.59/0.83         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.59/0.83           = (k3_xboole_0 @ X4 @ X5))),
% 0.59/0.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.83  thf(t36_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.59/0.83  thf('17', plain,
% 0.59/0.83      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.59/0.83      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.59/0.83  thf('18', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.59/0.83      inference('sup+', [status(thm)], ['16', '17'])).
% 0.59/0.83  thf('19', plain, ((r1_tarski @ sk_C @ sk_C)),
% 0.59/0.83      inference('sup+', [status(thm)], ['15', '18'])).
% 0.59/0.83  thf('20', plain,
% 0.59/0.83      (![X14 : $i, X16 : $i]:
% 0.59/0.83         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.59/0.83      inference('cnf', [status(esa)], [t3_subset])).
% 0.59/0.83  thf('21', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_C))),
% 0.59/0.83      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.83  thf('22', plain,
% 0.59/0.83      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.59/0.83         (((k9_subset_1 @ X6 @ X8 @ X7) = (k9_subset_1 @ X6 @ X7 @ X8))
% 0.59/0.83          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.59/0.83      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.59/0.83  thf('23', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((k9_subset_1 @ sk_C @ X0 @ sk_C) = (k9_subset_1 @ sk_C @ sk_C @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['21', '22'])).
% 0.59/0.83  thf('24', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_C))),
% 0.59/0.83      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.83  thf('25', plain,
% 0.59/0.83      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.59/0.83         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.59/0.83          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.59/0.83      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.59/0.83  thf('26', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((k9_subset_1 @ sk_C @ X0 @ sk_C) = (k3_xboole_0 @ X0 @ sk_C))),
% 0.59/0.83      inference('sup-', [status(thm)], ['24', '25'])).
% 0.59/0.83  thf('27', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((k3_xboole_0 @ X0 @ sk_C) = (k9_subset_1 @ sk_C @ sk_C @ X0))),
% 0.59/0.83      inference('demod', [status(thm)], ['23', '26'])).
% 0.59/0.83  thf('28', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.59/0.83      inference('sup+', [status(thm)], ['16', '17'])).
% 0.59/0.83  thf('29', plain,
% 0.59/0.83      (![X14 : $i, X16 : $i]:
% 0.59/0.83         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.59/0.83      inference('cnf', [status(esa)], [t3_subset])).
% 0.59/0.83  thf('30', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['28', '29'])).
% 0.59/0.83  thf('31', plain,
% 0.59/0.83      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.59/0.83         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.59/0.83          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.59/0.83      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.59/0.83  thf('32', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.83         ((k9_subset_1 @ X0 @ X2 @ (k3_xboole_0 @ X0 @ X1))
% 0.59/0.83           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['30', '31'])).
% 0.59/0.83  thf('33', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((k3_xboole_0 @ (k3_xboole_0 @ sk_C @ X0) @ sk_C)
% 0.59/0.83           = (k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.59/0.83      inference('sup+', [status(thm)], ['27', '32'])).
% 0.59/0.83  thf('34', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.59/0.83      inference('sup+', [status(thm)], ['16', '17'])).
% 0.59/0.83  thf('35', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.59/0.83      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.83  thf('36', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.59/0.83           = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('sup-', [status(thm)], ['34', '35'])).
% 0.59/0.83  thf('37', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((k3_xboole_0 @ sk_C @ X0)
% 0.59/0.83           = (k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.59/0.83      inference('demod', [status(thm)], ['33', '36'])).
% 0.59/0.83  thf('38', plain,
% 0.59/0.83      (((k3_xboole_0 @ sk_C @ sk_B)
% 0.59/0.83         = (k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.59/0.83      inference('sup+', [status(thm)], ['10', '37'])).
% 0.59/0.83  thf('39', plain,
% 0.59/0.83      (((k3_xboole_0 @ sk_C @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.59/0.83      inference('sup+', [status(thm)], ['6', '9'])).
% 0.59/0.83  thf('40', plain,
% 0.59/0.83      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.59/0.83         = (k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.59/0.83      inference('demod', [status(thm)], ['38', '39'])).
% 0.59/0.83  thf('41', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(dt_k1_pre_topc, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( ( l1_pre_topc @ A ) & 
% 0.59/0.83         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.83       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.59/0.83         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.59/0.83  thf('42', plain,
% 0.59/0.83      (![X17 : $i, X18 : $i]:
% 0.59/0.83         (~ (l1_pre_topc @ X17)
% 0.59/0.83          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.59/0.83          | (m1_pre_topc @ (k1_pre_topc @ X17 @ X18) @ X17))),
% 0.59/0.83      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.59/0.83  thf('43', plain,
% 0.59/0.83      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C) @ sk_A)
% 0.59/0.83        | ~ (l1_pre_topc @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['41', '42'])).
% 0.59/0.83  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('45', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C) @ sk_A)),
% 0.59/0.83      inference('demod', [status(thm)], ['43', '44'])).
% 0.59/0.83  thf('46', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['28', '29'])).
% 0.59/0.83  thf(t39_pre_topc, axiom,
% 0.59/0.83    (![A:$i]:
% 0.59/0.83     ( ( l1_pre_topc @ A ) =>
% 0.59/0.83       ( ![B:$i]:
% 0.59/0.83         ( ( m1_pre_topc @ B @ A ) =>
% 0.59/0.83           ( ![C:$i]:
% 0.59/0.83             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.59/0.83               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.59/0.83  thf('47', plain,
% 0.59/0.83      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.59/0.83         (~ (m1_pre_topc @ X21 @ X22)
% 0.59/0.83          | (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.59/0.83          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.59/0.83          | ~ (l1_pre_topc @ X22))),
% 0.59/0.83      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.59/0.83  thf('48', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.83         (~ (l1_pre_topc @ X2)
% 0.59/0.83          | (m1_subset_1 @ (k3_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ 
% 0.59/0.83             (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ X2))),
% 0.59/0.83      inference('sup-', [status(thm)], ['46', '47'])).
% 0.59/0.83  thf('49', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((m1_subset_1 @ 
% 0.59/0.83           (k3_xboole_0 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) @ X0) @ 
% 0.59/0.83           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.83          | ~ (l1_pre_topc @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['45', '48'])).
% 0.59/0.83  thf('50', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(t29_pre_topc, axiom,
% 0.59/0.83    (![A:$i]:
% 0.59/0.83     ( ( l1_pre_topc @ A ) =>
% 0.59/0.83       ( ![B:$i]:
% 0.59/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.83           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 0.59/0.83  thf('51', plain,
% 0.59/0.83      (![X19 : $i, X20 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.59/0.83          | ((u1_struct_0 @ (k1_pre_topc @ X20 @ X19)) = (X19))
% 0.59/0.83          | ~ (l1_pre_topc @ X20))),
% 0.59/0.83      inference('cnf', [status(esa)], [t29_pre_topc])).
% 0.59/0.83  thf('52', plain,
% 0.59/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.83        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['50', '51'])).
% 0.59/0.83  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('54', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C))),
% 0.59/0.83      inference('demod', [status(thm)], ['52', '53'])).
% 0.59/0.83  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('56', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (m1_subset_1 @ (k3_xboole_0 @ sk_C @ X0) @ 
% 0.59/0.83          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('demod', [status(thm)], ['49', '54', '55'])).
% 0.59/0.83  thf('57', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(t18_compts_1, axiom,
% 0.59/0.83    (![A:$i]:
% 0.59/0.83     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.83       ( ![B:$i]:
% 0.59/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.83           ( ![C:$i]:
% 0.59/0.83             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.83               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.59/0.83                   ( v4_pre_topc @ C @ A ) ) =>
% 0.59/0.83                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.59/0.83  thf('58', plain,
% 0.59/0.83      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.59/0.83          | ~ (v2_compts_1 @ X29 @ X30)
% 0.59/0.83          | ~ (r1_tarski @ X31 @ X29)
% 0.59/0.83          | ~ (v4_pre_topc @ X31 @ X30)
% 0.59/0.83          | (v2_compts_1 @ X31 @ X30)
% 0.59/0.83          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.59/0.83          | ~ (l1_pre_topc @ X30)
% 0.59/0.83          | ~ (v2_pre_topc @ X30))),
% 0.59/0.83      inference('cnf', [status(esa)], [t18_compts_1])).
% 0.59/0.83  thf('59', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (v2_pre_topc @ sk_A)
% 0.59/0.83          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.83          | (v2_compts_1 @ X0 @ sk_A)
% 0.59/0.83          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | ~ (r1_tarski @ X0 @ sk_C)
% 0.59/0.83          | ~ (v2_compts_1 @ sk_C @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['57', '58'])).
% 0.59/0.83  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('62', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('63', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.83          | (v2_compts_1 @ X0 @ sk_A)
% 0.59/0.83          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.59/0.83      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.59/0.83  thf('64', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ sk_C)
% 0.59/0.83          | ~ (v4_pre_topc @ (k3_xboole_0 @ sk_C @ X0) @ sk_A)
% 0.59/0.83          | (v2_compts_1 @ (k3_xboole_0 @ sk_C @ X0) @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['56', '63'])).
% 0.59/0.83  thf('65', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.59/0.83      inference('sup+', [status(thm)], ['16', '17'])).
% 0.59/0.83  thf('66', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (v4_pre_topc @ (k3_xboole_0 @ sk_C @ X0) @ sk_A)
% 0.59/0.83          | (v2_compts_1 @ (k3_xboole_0 @ sk_C @ X0) @ sk_A))),
% 0.59/0.83      inference('demod', [status(thm)], ['64', '65'])).
% 0.59/0.83  thf('67', plain,
% 0.59/0.83      ((~ (v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)
% 0.59/0.83        | (v2_compts_1 @ (k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 0.59/0.83           sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['40', '66'])).
% 0.59/0.83  thf('68', plain,
% 0.59/0.83      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.59/0.83         = (k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.59/0.83      inference('demod', [status(thm)], ['38', '39'])).
% 0.59/0.83  thf('69', plain,
% 0.59/0.83      ((~ (v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)
% 0.59/0.83        | (v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.59/0.83      inference('demod', [status(thm)], ['67', '68'])).
% 0.59/0.83  thf('70', plain,
% 0.59/0.83      (~ (v2_compts_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.59/0.83          sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('71', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.59/0.83           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.59/0.83      inference('sup-', [status(thm)], ['7', '8'])).
% 0.59/0.83  thf('72', plain, (~ (v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.59/0.83      inference('demod', [status(thm)], ['70', '71'])).
% 0.59/0.83  thf('73', plain, (~ (v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.59/0.83      inference('clc', [status(thm)], ['69', '72'])).
% 0.59/0.83  thf('74', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('75', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(t35_tops_1, axiom,
% 0.59/0.83    (![A:$i]:
% 0.59/0.83     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.83       ( ![B:$i]:
% 0.59/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.83           ( ![C:$i]:
% 0.59/0.83             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.83               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.59/0.83                 ( v4_pre_topc @
% 0.59/0.83                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.59/0.83  thf('76', plain,
% 0.59/0.83      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.59/0.83          | ~ (v4_pre_topc @ X24 @ X25)
% 0.59/0.83          | ~ (v4_pre_topc @ X26 @ X25)
% 0.59/0.83          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ X25) @ X24 @ X26) @ 
% 0.59/0.83             X25)
% 0.59/0.83          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.59/0.83          | ~ (l1_pre_topc @ X25)
% 0.59/0.83          | ~ (v2_pre_topc @ X25))),
% 0.59/0.83      inference('cnf', [status(esa)], [t35_tops_1])).
% 0.59/0.83  thf('77', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (v2_pre_topc @ sk_A)
% 0.59/0.83          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.83          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.59/0.83             sk_A)
% 0.59/0.83          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['75', '76'])).
% 0.59/0.83  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('80', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.83          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.59/0.83             sk_A)
% 0.59/0.83          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.59/0.83      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.59/0.83  thf('81', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((k3_xboole_0 @ X0 @ sk_B)
% 0.59/0.83           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.59/0.83      inference('demod', [status(thm)], ['2', '5'])).
% 0.59/0.83  thf('82', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(t16_compts_1, axiom,
% 0.59/0.83    (![A:$i]:
% 0.59/0.83     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.83       ( ![B:$i]:
% 0.59/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.83           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.59/0.83             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.59/0.83  thf('83', plain,
% 0.59/0.83      (![X27 : $i, X28 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.59/0.83          | (v4_pre_topc @ X27 @ X28)
% 0.59/0.83          | ~ (v2_compts_1 @ X27 @ X28)
% 0.59/0.83          | ~ (v8_pre_topc @ X28)
% 0.59/0.83          | ~ (l1_pre_topc @ X28)
% 0.59/0.83          | ~ (v2_pre_topc @ X28))),
% 0.59/0.83      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.59/0.83  thf('84', plain,
% 0.59/0.83      ((~ (v2_pre_topc @ sk_A)
% 0.59/0.83        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.83        | ~ (v8_pre_topc @ sk_A)
% 0.59/0.83        | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.59/0.83        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['82', '83'])).
% 0.59/0.83  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('87', plain, ((v8_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('88', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('89', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.59/0.83      inference('demod', [status(thm)], ['84', '85', '86', '87', '88'])).
% 0.59/0.83  thf('90', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.83          | (v4_pre_topc @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A)
% 0.59/0.83          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.59/0.83      inference('demod', [status(thm)], ['80', '81', '89'])).
% 0.59/0.83  thf('91', plain,
% 0.59/0.83      ((~ (v4_pre_topc @ sk_C @ sk_A)
% 0.59/0.83        | (v4_pre_topc @ (k3_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['74', '90'])).
% 0.59/0.83  thf('92', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('93', plain,
% 0.59/0.83      (![X27 : $i, X28 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.59/0.83          | (v4_pre_topc @ X27 @ X28)
% 0.59/0.83          | ~ (v2_compts_1 @ X27 @ X28)
% 0.59/0.83          | ~ (v8_pre_topc @ X28)
% 0.59/0.83          | ~ (l1_pre_topc @ X28)
% 0.59/0.83          | ~ (v2_pre_topc @ X28))),
% 0.59/0.83      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.59/0.83  thf('94', plain,
% 0.59/0.83      ((~ (v2_pre_topc @ sk_A)
% 0.59/0.83        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.83        | ~ (v8_pre_topc @ sk_A)
% 0.59/0.83        | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.59/0.83        | (v4_pre_topc @ sk_C @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['92', '93'])).
% 0.59/0.83  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('97', plain, ((v8_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('98', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('99', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.59/0.83      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 0.59/0.83  thf('100', plain,
% 0.59/0.83      (((k3_xboole_0 @ sk_C @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.59/0.83      inference('sup+', [status(thm)], ['6', '9'])).
% 0.59/0.83  thf('101', plain, ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.59/0.83      inference('demod', [status(thm)], ['91', '99', '100'])).
% 0.59/0.83  thf('102', plain, ($false), inference('demod', [status(thm)], ['73', '101'])).
% 0.59/0.83  
% 0.59/0.83  % SZS output end Refutation
% 0.59/0.83  
% 0.59/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

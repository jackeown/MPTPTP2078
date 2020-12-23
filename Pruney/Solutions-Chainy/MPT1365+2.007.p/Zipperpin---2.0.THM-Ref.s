%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pjSfFHnmE0

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:36 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 150 expanded)
%              Number of leaves         :   27 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  666 (1971 expanded)
%              Number of equality atoms :   15 (  30 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( v4_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v4_pre_topc @ ( k3_xboole_0 @ X17 @ X19 ) @ X18 ) ) ),
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
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v4_pre_topc @ X20 @ X21 )
      | ~ ( v2_compts_1 @ X20 @ X21 )
      | ~ ( v8_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('14',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','19'])).

thf('21',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v4_pre_topc @ X20 @ X21 )
      | ~ ( v2_compts_1 @ X20 @ X21 )
      | ~ ( v8_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('24',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_C @ sk_A )
    | ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

thf('30',plain,(
    v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['21','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,
    ( ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    = sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X8 @ X7 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['35','48'])).

thf('50',plain,(
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

thf('51',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_compts_1 @ X22 @ X23 )
      | ~ ( r1_tarski @ X24 @ X22 )
      | ~ ( v4_pre_topc @ X24 @ X23 )
      | ( v2_compts_1 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t18_compts_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_compts_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_C )
      | ~ ( v4_pre_topc @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('59',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,(
    v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['30','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['4','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pjSfFHnmE0
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:51:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.84/1.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.84/1.03  % Solved by: fo/fo7.sh
% 0.84/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.03  % done 532 iterations in 0.571s
% 0.84/1.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.84/1.03  % SZS output start Refutation
% 0.84/1.03  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.84/1.03  thf(sk_C_type, type, sk_C: $i).
% 0.84/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.84/1.03  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.84/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.03  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.84/1.03  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.84/1.03  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.84/1.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.84/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.84/1.03  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.84/1.03  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.84/1.03  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.84/1.03  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.84/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.03  thf(t20_compts_1, conjecture,
% 0.84/1.03    (![A:$i]:
% 0.84/1.03     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.03       ( ![B:$i]:
% 0.84/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.03           ( ![C:$i]:
% 0.84/1.03             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.03               ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.84/1.03                   ( v2_compts_1 @ C @ A ) ) =>
% 0.84/1.03                 ( v2_compts_1 @
% 0.84/1.03                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.84/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.03    (~( ![A:$i]:
% 0.84/1.03        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.03          ( ![B:$i]:
% 0.84/1.03            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.03              ( ![C:$i]:
% 0.84/1.03                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.03                  ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.84/1.03                      ( v2_compts_1 @ C @ A ) ) =>
% 0.84/1.03                    ( v2_compts_1 @
% 0.84/1.03                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.84/1.03    inference('cnf.neg', [status(esa)], [t20_compts_1])).
% 0.84/1.03  thf('0', plain,
% 0.84/1.03      (~ (v2_compts_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.84/1.03          sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('1', plain,
% 0.84/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf(redefinition_k9_subset_1, axiom,
% 0.84/1.03    (![A:$i,B:$i,C:$i]:
% 0.84/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.84/1.03       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.84/1.03  thf('2', plain,
% 0.84/1.03      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.84/1.03         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.84/1.03          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.84/1.03      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.84/1.03  thf('3', plain,
% 0.84/1.03      (![X0 : $i]:
% 0.84/1.03         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.84/1.03           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.84/1.03      inference('sup-', [status(thm)], ['1', '2'])).
% 0.84/1.03  thf('4', plain, (~ (v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.84/1.03      inference('demod', [status(thm)], ['0', '3'])).
% 0.84/1.03  thf('5', plain,
% 0.84/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('6', plain,
% 0.84/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf(fc4_tops_1, axiom,
% 0.84/1.03    (![A:$i,B:$i,C:$i]:
% 0.84/1.03     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v4_pre_topc @ B @ A ) & 
% 0.84/1.03         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.84/1.03         ( v4_pre_topc @ C @ A ) & 
% 0.84/1.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.84/1.03       ( v4_pre_topc @ ( k3_xboole_0 @ B @ C ) @ A ) ))).
% 0.84/1.03  thf('7', plain,
% 0.84/1.03      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.84/1.03         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.84/1.03          | ~ (v4_pre_topc @ X17 @ X18)
% 0.84/1.03          | ~ (l1_pre_topc @ X18)
% 0.84/1.03          | ~ (v2_pre_topc @ X18)
% 0.84/1.03          | ~ (v4_pre_topc @ X19 @ X18)
% 0.84/1.03          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.84/1.03          | (v4_pre_topc @ (k3_xboole_0 @ X17 @ X19) @ X18))),
% 0.84/1.03      inference('cnf', [status(esa)], [fc4_tops_1])).
% 0.84/1.03  thf('8', plain,
% 0.84/1.03      (![X0 : $i]:
% 0.84/1.03         ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.84/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.03          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.84/1.03          | ~ (v2_pre_topc @ sk_A)
% 0.84/1.03          | ~ (l1_pre_topc @ sk_A)
% 0.84/1.03          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.84/1.03      inference('sup-', [status(thm)], ['6', '7'])).
% 0.84/1.03  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('11', plain,
% 0.84/1.03      (![X0 : $i]:
% 0.84/1.03         ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.84/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.03          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.84/1.03          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.84/1.03      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.84/1.03  thf('12', plain,
% 0.84/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf(t16_compts_1, axiom,
% 0.84/1.03    (![A:$i]:
% 0.84/1.03     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.03       ( ![B:$i]:
% 0.84/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.03           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.84/1.03             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.84/1.03  thf('13', plain,
% 0.84/1.03      (![X20 : $i, X21 : $i]:
% 0.84/1.03         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.84/1.03          | (v4_pre_topc @ X20 @ X21)
% 0.84/1.03          | ~ (v2_compts_1 @ X20 @ X21)
% 0.84/1.03          | ~ (v8_pre_topc @ X21)
% 0.84/1.03          | ~ (l1_pre_topc @ X21)
% 0.84/1.03          | ~ (v2_pre_topc @ X21))),
% 0.84/1.03      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.84/1.03  thf('14', plain,
% 0.84/1.03      ((~ (v2_pre_topc @ sk_A)
% 0.84/1.03        | ~ (l1_pre_topc @ sk_A)
% 0.84/1.03        | ~ (v8_pre_topc @ sk_A)
% 0.84/1.03        | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.84/1.03        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.84/1.03      inference('sup-', [status(thm)], ['12', '13'])).
% 0.84/1.03  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('17', plain, ((v8_pre_topc @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('18', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('19', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.84/1.03      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.84/1.03  thf('20', plain,
% 0.84/1.03      (![X0 : $i]:
% 0.84/1.03         ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.84/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.03          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.84/1.03      inference('demod', [status(thm)], ['11', '19'])).
% 0.84/1.03  thf('21', plain,
% 0.84/1.03      ((~ (v4_pre_topc @ sk_C @ sk_A)
% 0.84/1.03        | (v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.84/1.03      inference('sup-', [status(thm)], ['5', '20'])).
% 0.84/1.03  thf('22', plain,
% 0.84/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('23', plain,
% 0.84/1.03      (![X20 : $i, X21 : $i]:
% 0.84/1.03         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.84/1.03          | (v4_pre_topc @ X20 @ X21)
% 0.84/1.03          | ~ (v2_compts_1 @ X20 @ X21)
% 0.84/1.03          | ~ (v8_pre_topc @ X21)
% 0.84/1.03          | ~ (l1_pre_topc @ X21)
% 0.84/1.03          | ~ (v2_pre_topc @ X21))),
% 0.84/1.03      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.84/1.03  thf('24', plain,
% 0.84/1.03      ((~ (v2_pre_topc @ sk_A)
% 0.84/1.03        | ~ (l1_pre_topc @ sk_A)
% 0.84/1.03        | ~ (v8_pre_topc @ sk_A)
% 0.84/1.03        | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.84/1.03        | (v4_pre_topc @ sk_C @ sk_A))),
% 0.84/1.03      inference('sup-', [status(thm)], ['22', '23'])).
% 0.84/1.03  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('27', plain, ((v8_pre_topc @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('28', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('29', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.84/1.03      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 0.84/1.03  thf('30', plain, ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.84/1.03      inference('demod', [status(thm)], ['21', '29'])).
% 0.84/1.03  thf('31', plain,
% 0.84/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf(t3_subset, axiom,
% 0.84/1.03    (![A:$i,B:$i]:
% 0.84/1.03     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.84/1.03  thf('32', plain,
% 0.84/1.03      (![X14 : $i, X15 : $i]:
% 0.84/1.03         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.84/1.03      inference('cnf', [status(esa)], [t3_subset])).
% 0.84/1.03  thf('33', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.84/1.03      inference('sup-', [status(thm)], ['31', '32'])).
% 0.84/1.03  thf(t28_xboole_1, axiom,
% 0.84/1.03    (![A:$i,B:$i]:
% 0.84/1.03     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.84/1.03  thf('34', plain,
% 0.84/1.03      (![X5 : $i, X6 : $i]:
% 0.84/1.03         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.84/1.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.84/1.03  thf('35', plain, (((k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A)) = (sk_C))),
% 0.84/1.03      inference('sup-', [status(thm)], ['33', '34'])).
% 0.84/1.03  thf(commutativity_k2_tarski, axiom,
% 0.84/1.03    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.84/1.03  thf('36', plain,
% 0.84/1.03      (![X7 : $i, X8 : $i]: ((k2_tarski @ X8 @ X7) = (k2_tarski @ X7 @ X8))),
% 0.84/1.03      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.84/1.03  thf(t12_setfam_1, axiom,
% 0.84/1.03    (![A:$i,B:$i]:
% 0.84/1.03     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.84/1.03  thf('37', plain,
% 0.84/1.03      (![X12 : $i, X13 : $i]:
% 0.84/1.03         ((k1_setfam_1 @ (k2_tarski @ X12 @ X13)) = (k3_xboole_0 @ X12 @ X13))),
% 0.84/1.03      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.84/1.03  thf('38', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i]:
% 0.84/1.03         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.03      inference('sup+', [status(thm)], ['36', '37'])).
% 0.84/1.03  thf('39', plain,
% 0.84/1.03      (![X12 : $i, X13 : $i]:
% 0.84/1.03         ((k1_setfam_1 @ (k2_tarski @ X12 @ X13)) = (k3_xboole_0 @ X12 @ X13))),
% 0.84/1.03      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.84/1.03  thf('40', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.03      inference('sup+', [status(thm)], ['38', '39'])).
% 0.84/1.03  thf('41', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.03      inference('sup+', [status(thm)], ['38', '39'])).
% 0.84/1.03  thf(t17_xboole_1, axiom,
% 0.84/1.03    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.84/1.03  thf('42', plain,
% 0.84/1.03      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.84/1.03      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.84/1.03  thf(t108_xboole_1, axiom,
% 0.84/1.03    (![A:$i,B:$i,C:$i]:
% 0.84/1.03     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 0.84/1.03  thf('43', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.03         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X0 @ X2) @ X1))),
% 0.84/1.03      inference('cnf', [status(esa)], [t108_xboole_1])).
% 0.84/1.03  thf('44', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.03         (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2) @ X0)),
% 0.84/1.03      inference('sup-', [status(thm)], ['42', '43'])).
% 0.84/1.03  thf('45', plain,
% 0.84/1.03      (![X14 : $i, X16 : $i]:
% 0.84/1.03         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.84/1.03      inference('cnf', [status(esa)], [t3_subset])).
% 0.84/1.03  thf('46', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.03         (m1_subset_1 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ X1) @ 
% 0.84/1.03          (k1_zfmisc_1 @ X0))),
% 0.84/1.03      inference('sup-', [status(thm)], ['44', '45'])).
% 0.84/1.03  thf('47', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.03         (m1_subset_1 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.84/1.03          (k1_zfmisc_1 @ X1))),
% 0.84/1.03      inference('sup+', [status(thm)], ['41', '46'])).
% 0.84/1.03  thf('48', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.03         (m1_subset_1 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.84/1.03          (k1_zfmisc_1 @ X0))),
% 0.84/1.03      inference('sup+', [status(thm)], ['40', '47'])).
% 0.84/1.03  thf('49', plain,
% 0.84/1.03      (![X0 : $i]:
% 0.84/1.03         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 0.84/1.03          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.03      inference('sup+', [status(thm)], ['35', '48'])).
% 0.84/1.03  thf('50', plain,
% 0.84/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf(t18_compts_1, axiom,
% 0.84/1.03    (![A:$i]:
% 0.84/1.03     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.03       ( ![B:$i]:
% 0.84/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.03           ( ![C:$i]:
% 0.84/1.03             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.03               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.84/1.03                   ( v4_pre_topc @ C @ A ) ) =>
% 0.84/1.03                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.84/1.03  thf('51', plain,
% 0.84/1.03      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.84/1.03         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.84/1.03          | ~ (v2_compts_1 @ X22 @ X23)
% 0.84/1.03          | ~ (r1_tarski @ X24 @ X22)
% 0.84/1.03          | ~ (v4_pre_topc @ X24 @ X23)
% 0.84/1.03          | (v2_compts_1 @ X24 @ X23)
% 0.84/1.03          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.84/1.03          | ~ (l1_pre_topc @ X23)
% 0.84/1.03          | ~ (v2_pre_topc @ X23))),
% 0.84/1.03      inference('cnf', [status(esa)], [t18_compts_1])).
% 0.84/1.03  thf('52', plain,
% 0.84/1.03      (![X0 : $i]:
% 0.84/1.03         (~ (v2_pre_topc @ sk_A)
% 0.84/1.03          | ~ (l1_pre_topc @ sk_A)
% 0.84/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.03          | (v2_compts_1 @ X0 @ sk_A)
% 0.84/1.03          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.84/1.03          | ~ (r1_tarski @ X0 @ sk_C)
% 0.84/1.03          | ~ (v2_compts_1 @ sk_C @ sk_A))),
% 0.84/1.03      inference('sup-', [status(thm)], ['50', '51'])).
% 0.84/1.03  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('55', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('56', plain,
% 0.84/1.03      (![X0 : $i]:
% 0.84/1.03         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.03          | (v2_compts_1 @ X0 @ sk_A)
% 0.84/1.03          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.84/1.03          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.84/1.03      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.84/1.03  thf('57', plain,
% 0.84/1.03      (![X0 : $i]:
% 0.84/1.03         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_C)
% 0.84/1.03          | ~ (v4_pre_topc @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)
% 0.84/1.03          | (v2_compts_1 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A))),
% 0.84/1.03      inference('sup-', [status(thm)], ['49', '56'])).
% 0.84/1.03  thf('58', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.03      inference('sup+', [status(thm)], ['38', '39'])).
% 0.84/1.03  thf('59', plain,
% 0.84/1.03      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.84/1.03      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.84/1.03  thf('60', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.84/1.03      inference('sup+', [status(thm)], ['58', '59'])).
% 0.84/1.03  thf('61', plain,
% 0.84/1.03      (![X0 : $i]:
% 0.84/1.03         (~ (v4_pre_topc @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)
% 0.84/1.03          | (v2_compts_1 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A))),
% 0.84/1.03      inference('demod', [status(thm)], ['57', '60'])).
% 0.84/1.03  thf('62', plain, ((v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.84/1.03      inference('sup-', [status(thm)], ['30', '61'])).
% 0.84/1.03  thf('63', plain, ($false), inference('demod', [status(thm)], ['4', '62'])).
% 0.84/1.03  
% 0.84/1.03  % SZS output end Refutation
% 0.84/1.03  
% 0.84/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

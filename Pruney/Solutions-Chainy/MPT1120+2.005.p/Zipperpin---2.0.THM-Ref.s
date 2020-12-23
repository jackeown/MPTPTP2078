%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GHtRzvEGvg

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:18 EST 2020

% Result     : Theorem 15.37s
% Output     : Refutation 15.37s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 148 expanded)
%              Number of leaves         :   23 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  715 (1595 expanded)
%              Number of equality atoms :   16 (  54 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t51_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( r1_tarski @ ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_pre_topc])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ sk_C ) )
      = ( k3_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','11'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( r1_tarski @ X20 @ X22 )
      | ( r1_tarski @ ( k2_pre_topc @ X21 @ X20 ) @ ( k2_pre_topc @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_C )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['17','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( r1_tarski @ X20 @ X22 )
      | ( r1_tarski @ ( k2_pre_topc @ X21 @ X20 ) @ ( k2_pre_topc @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ X1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('55',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X1 ) )
      | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('59',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['12','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GHtRzvEGvg
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:16:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 15.37/15.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 15.37/15.62  % Solved by: fo/fo7.sh
% 15.37/15.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.37/15.62  % done 10241 iterations in 15.181s
% 15.37/15.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 15.37/15.62  % SZS output start Refutation
% 15.37/15.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 15.37/15.62  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 15.37/15.62  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 15.37/15.62  thf(sk_B_type, type, sk_B: $i).
% 15.37/15.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 15.37/15.62  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 15.37/15.62  thf(sk_A_type, type, sk_A: $i).
% 15.37/15.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 15.37/15.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 15.37/15.62  thf(sk_C_type, type, sk_C: $i).
% 15.37/15.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 15.37/15.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 15.37/15.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 15.37/15.62  thf(t51_pre_topc, conjecture,
% 15.37/15.62    (![A:$i]:
% 15.37/15.62     ( ( l1_pre_topc @ A ) =>
% 15.37/15.62       ( ![B:$i]:
% 15.37/15.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.37/15.62           ( ![C:$i]:
% 15.37/15.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.37/15.62               ( r1_tarski @
% 15.37/15.62                 ( k2_pre_topc @
% 15.37/15.62                   A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 15.37/15.62                 ( k9_subset_1 @
% 15.37/15.62                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 15.37/15.62                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 15.37/15.62  thf(zf_stmt_0, negated_conjecture,
% 15.37/15.62    (~( ![A:$i]:
% 15.37/15.62        ( ( l1_pre_topc @ A ) =>
% 15.37/15.62          ( ![B:$i]:
% 15.37/15.62            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.37/15.62              ( ![C:$i]:
% 15.37/15.62                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.37/15.62                  ( r1_tarski @
% 15.37/15.62                    ( k2_pre_topc @
% 15.37/15.62                      A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 15.37/15.62                    ( k9_subset_1 @
% 15.37/15.62                      ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 15.37/15.62                      ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) )),
% 15.37/15.62    inference('cnf.neg', [status(esa)], [t51_pre_topc])).
% 15.37/15.62  thf('0', plain,
% 15.37/15.62      (~ (r1_tarski @ 
% 15.37/15.62          (k2_pre_topc @ sk_A @ 
% 15.37/15.62           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 15.37/15.62          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 15.37/15.62           (k2_pre_topc @ sk_A @ sk_C)))),
% 15.37/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.37/15.62  thf('1', plain,
% 15.37/15.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.37/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.37/15.62  thf(redefinition_k9_subset_1, axiom,
% 15.37/15.62    (![A:$i,B:$i,C:$i]:
% 15.37/15.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 15.37/15.62       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 15.37/15.62  thf('2', plain,
% 15.37/15.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 15.37/15.62         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 15.37/15.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 15.37/15.62      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 15.37/15.62  thf('3', plain,
% 15.37/15.62      (![X0 : $i]:
% 15.37/15.62         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 15.37/15.62           = (k3_xboole_0 @ X0 @ sk_C))),
% 15.37/15.62      inference('sup-', [status(thm)], ['1', '2'])).
% 15.37/15.62  thf('4', plain,
% 15.37/15.62      (~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 15.37/15.62          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 15.37/15.62           (k2_pre_topc @ sk_A @ sk_C)))),
% 15.37/15.62      inference('demod', [status(thm)], ['0', '3'])).
% 15.37/15.62  thf('5', plain,
% 15.37/15.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.37/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.37/15.62  thf(dt_k2_pre_topc, axiom,
% 15.37/15.62    (![A:$i,B:$i]:
% 15.37/15.62     ( ( ( l1_pre_topc @ A ) & 
% 15.37/15.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 15.37/15.62       ( m1_subset_1 @
% 15.37/15.62         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 15.37/15.62  thf('6', plain,
% 15.37/15.62      (![X18 : $i, X19 : $i]:
% 15.37/15.62         (~ (l1_pre_topc @ X18)
% 15.37/15.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 15.37/15.62          | (m1_subset_1 @ (k2_pre_topc @ X18 @ X19) @ 
% 15.37/15.62             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 15.37/15.62      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 15.37/15.62  thf('7', plain,
% 15.37/15.62      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 15.37/15.62         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 15.37/15.62        | ~ (l1_pre_topc @ sk_A))),
% 15.37/15.62      inference('sup-', [status(thm)], ['5', '6'])).
% 15.37/15.62  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 15.37/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.37/15.62  thf('9', plain,
% 15.37/15.62      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 15.37/15.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.37/15.62      inference('demod', [status(thm)], ['7', '8'])).
% 15.37/15.62  thf('10', plain,
% 15.37/15.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 15.37/15.62         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 15.37/15.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 15.37/15.62      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 15.37/15.62  thf('11', plain,
% 15.37/15.62      (![X0 : $i]:
% 15.37/15.62         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 15.37/15.62           (k2_pre_topc @ sk_A @ sk_C))
% 15.37/15.62           = (k3_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ sk_C)))),
% 15.37/15.62      inference('sup-', [status(thm)], ['9', '10'])).
% 15.37/15.62  thf('12', plain,
% 15.37/15.62      (~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 15.37/15.62          (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 15.37/15.62           (k2_pre_topc @ sk_A @ sk_C)))),
% 15.37/15.62      inference('demod', [status(thm)], ['4', '11'])).
% 15.37/15.62  thf(commutativity_k2_tarski, axiom,
% 15.37/15.62    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 15.37/15.62  thf('13', plain,
% 15.37/15.62      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 15.37/15.62      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 15.37/15.62  thf(t12_setfam_1, axiom,
% 15.37/15.62    (![A:$i,B:$i]:
% 15.37/15.62     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 15.37/15.62  thf('14', plain,
% 15.37/15.62      (![X13 : $i, X14 : $i]:
% 15.37/15.62         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 15.37/15.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 15.37/15.62  thf('15', plain,
% 15.37/15.62      (![X0 : $i, X1 : $i]:
% 15.37/15.62         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 15.37/15.62      inference('sup+', [status(thm)], ['13', '14'])).
% 15.37/15.62  thf('16', plain,
% 15.37/15.62      (![X13 : $i, X14 : $i]:
% 15.37/15.62         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 15.37/15.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 15.37/15.62  thf('17', plain,
% 15.37/15.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.37/15.62      inference('sup+', [status(thm)], ['15', '16'])).
% 15.37/15.62  thf('18', plain,
% 15.37/15.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.37/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.37/15.62  thf('19', plain,
% 15.37/15.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.37/15.62      inference('sup+', [status(thm)], ['15', '16'])).
% 15.37/15.62  thf('20', plain,
% 15.37/15.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.37/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.37/15.62  thf(t3_subset, axiom,
% 15.37/15.62    (![A:$i,B:$i]:
% 15.37/15.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 15.37/15.62  thf('21', plain,
% 15.37/15.62      (![X15 : $i, X16 : $i]:
% 15.37/15.62         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 15.37/15.62      inference('cnf', [status(esa)], [t3_subset])).
% 15.37/15.62  thf('22', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 15.37/15.62      inference('sup-', [status(thm)], ['20', '21'])).
% 15.37/15.62  thf(t108_xboole_1, axiom,
% 15.37/15.62    (![A:$i,B:$i,C:$i]:
% 15.37/15.62     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 15.37/15.62  thf('23', plain,
% 15.37/15.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.37/15.62         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X0 @ X2) @ X1))),
% 15.37/15.62      inference('cnf', [status(esa)], [t108_xboole_1])).
% 15.37/15.62  thf('24', plain,
% 15.37/15.62      (![X0 : $i]:
% 15.37/15.62         (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ (u1_struct_0 @ sk_A))),
% 15.37/15.62      inference('sup-', [status(thm)], ['22', '23'])).
% 15.37/15.62  thf('25', plain,
% 15.37/15.62      (![X0 : $i]:
% 15.37/15.62         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 15.37/15.62      inference('sup+', [status(thm)], ['19', '24'])).
% 15.37/15.62  thf('26', plain,
% 15.37/15.62      (![X15 : $i, X17 : $i]:
% 15.37/15.62         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 15.37/15.62      inference('cnf', [status(esa)], [t3_subset])).
% 15.37/15.62  thf('27', plain,
% 15.37/15.62      (![X0 : $i]:
% 15.37/15.62         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 15.37/15.62          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.37/15.62      inference('sup-', [status(thm)], ['25', '26'])).
% 15.37/15.62  thf(t49_pre_topc, axiom,
% 15.37/15.62    (![A:$i]:
% 15.37/15.62     ( ( l1_pre_topc @ A ) =>
% 15.37/15.62       ( ![B:$i]:
% 15.37/15.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.37/15.62           ( ![C:$i]:
% 15.37/15.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 15.37/15.62               ( ( r1_tarski @ B @ C ) =>
% 15.37/15.62                 ( r1_tarski @
% 15.37/15.62                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 15.37/15.62  thf('28', plain,
% 15.37/15.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 15.37/15.62         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 15.37/15.62          | ~ (r1_tarski @ X20 @ X22)
% 15.37/15.62          | (r1_tarski @ (k2_pre_topc @ X21 @ X20) @ (k2_pre_topc @ X21 @ X22))
% 15.37/15.62          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 15.37/15.62          | ~ (l1_pre_topc @ X21))),
% 15.37/15.62      inference('cnf', [status(esa)], [t49_pre_topc])).
% 15.37/15.62  thf('29', plain,
% 15.37/15.62      (![X0 : $i, X1 : $i]:
% 15.37/15.62         (~ (l1_pre_topc @ sk_A)
% 15.37/15.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 15.37/15.62          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 15.37/15.62             (k2_pre_topc @ sk_A @ X1))
% 15.37/15.62          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ X1))),
% 15.37/15.62      inference('sup-', [status(thm)], ['27', '28'])).
% 15.37/15.62  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 15.37/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.37/15.62  thf('31', plain,
% 15.37/15.62      (![X0 : $i, X1 : $i]:
% 15.37/15.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 15.37/15.62          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 15.37/15.62             (k2_pre_topc @ sk_A @ X1))
% 15.37/15.62          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ X1))),
% 15.37/15.62      inference('demod', [status(thm)], ['29', '30'])).
% 15.37/15.62  thf('32', plain,
% 15.37/15.62      (![X0 : $i]:
% 15.37/15.62         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_C)
% 15.37/15.62          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 15.37/15.62             (k2_pre_topc @ sk_A @ sk_C)))),
% 15.37/15.62      inference('sup-', [status(thm)], ['18', '31'])).
% 15.37/15.62  thf('33', plain,
% 15.37/15.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.37/15.62      inference('sup+', [status(thm)], ['15', '16'])).
% 15.37/15.62  thf(t17_xboole_1, axiom,
% 15.37/15.62    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 15.37/15.62  thf('34', plain,
% 15.37/15.62      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 15.37/15.62      inference('cnf', [status(esa)], [t17_xboole_1])).
% 15.37/15.62  thf('35', plain,
% 15.37/15.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 15.37/15.62      inference('sup+', [status(thm)], ['33', '34'])).
% 15.37/15.62  thf('36', plain,
% 15.37/15.62      (![X0 : $i]:
% 15.37/15.62         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 15.37/15.62          (k2_pre_topc @ sk_A @ sk_C))),
% 15.37/15.62      inference('demod', [status(thm)], ['32', '35'])).
% 15.37/15.62  thf('37', plain,
% 15.37/15.62      (![X0 : $i]:
% 15.37/15.62         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0)) @ 
% 15.37/15.62          (k2_pre_topc @ sk_A @ sk_C))),
% 15.37/15.62      inference('sup+', [status(thm)], ['17', '36'])).
% 15.37/15.62  thf('38', plain,
% 15.37/15.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.37/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.37/15.62  thf('39', plain,
% 15.37/15.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.37/15.62      inference('sup+', [status(thm)], ['15', '16'])).
% 15.37/15.62  thf('40', plain,
% 15.37/15.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.37/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.37/15.62  thf('41', plain,
% 15.37/15.62      (![X15 : $i, X16 : $i]:
% 15.37/15.62         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 15.37/15.62      inference('cnf', [status(esa)], [t3_subset])).
% 15.37/15.62  thf('42', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 15.37/15.62      inference('sup-', [status(thm)], ['40', '41'])).
% 15.37/15.62  thf('43', plain,
% 15.37/15.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.37/15.62         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X0 @ X2) @ X1))),
% 15.37/15.62      inference('cnf', [status(esa)], [t108_xboole_1])).
% 15.37/15.62  thf('44', plain,
% 15.37/15.62      (![X0 : $i]:
% 15.37/15.62         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 15.37/15.62      inference('sup-', [status(thm)], ['42', '43'])).
% 15.37/15.62  thf('45', plain,
% 15.37/15.62      (![X0 : $i]:
% 15.37/15.62         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 15.37/15.62      inference('sup+', [status(thm)], ['39', '44'])).
% 15.37/15.62  thf('46', plain,
% 15.37/15.62      (![X15 : $i, X17 : $i]:
% 15.37/15.62         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 15.37/15.62      inference('cnf', [status(esa)], [t3_subset])).
% 15.37/15.62  thf('47', plain,
% 15.37/15.62      (![X0 : $i]:
% 15.37/15.62         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 15.37/15.62          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 15.37/15.62      inference('sup-', [status(thm)], ['45', '46'])).
% 15.37/15.62  thf('48', plain,
% 15.37/15.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 15.37/15.62         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 15.37/15.62          | ~ (r1_tarski @ X20 @ X22)
% 15.37/15.62          | (r1_tarski @ (k2_pre_topc @ X21 @ X20) @ (k2_pre_topc @ X21 @ X22))
% 15.37/15.62          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 15.37/15.62          | ~ (l1_pre_topc @ X21))),
% 15.37/15.62      inference('cnf', [status(esa)], [t49_pre_topc])).
% 15.37/15.62  thf('49', plain,
% 15.37/15.62      (![X0 : $i, X1 : $i]:
% 15.37/15.62         (~ (l1_pre_topc @ sk_A)
% 15.37/15.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 15.37/15.62          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 15.37/15.62             (k2_pre_topc @ sk_A @ X1))
% 15.37/15.62          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ X1))),
% 15.37/15.62      inference('sup-', [status(thm)], ['47', '48'])).
% 15.37/15.62  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 15.37/15.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.37/15.62  thf('51', plain,
% 15.37/15.62      (![X0 : $i, X1 : $i]:
% 15.37/15.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 15.37/15.62          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 15.37/15.62             (k2_pre_topc @ sk_A @ X1))
% 15.37/15.62          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ X1))),
% 15.37/15.62      inference('demod', [status(thm)], ['49', '50'])).
% 15.37/15.62  thf('52', plain,
% 15.37/15.62      (![X0 : $i]:
% 15.37/15.62         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B)
% 15.37/15.62          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 15.37/15.62             (k2_pre_topc @ sk_A @ sk_B)))),
% 15.37/15.62      inference('sup-', [status(thm)], ['38', '51'])).
% 15.37/15.62  thf('53', plain,
% 15.37/15.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 15.37/15.62      inference('sup+', [status(thm)], ['33', '34'])).
% 15.37/15.62  thf('54', plain,
% 15.37/15.62      (![X0 : $i]:
% 15.37/15.62         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 15.37/15.62          (k2_pre_topc @ sk_A @ sk_B))),
% 15.37/15.62      inference('demod', [status(thm)], ['52', '53'])).
% 15.37/15.62  thf(t19_xboole_1, axiom,
% 15.37/15.62    (![A:$i,B:$i,C:$i]:
% 15.37/15.62     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 15.37/15.62       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 15.37/15.62  thf('55', plain,
% 15.37/15.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 15.37/15.62         (~ (r1_tarski @ X5 @ X6)
% 15.37/15.62          | ~ (r1_tarski @ X5 @ X7)
% 15.37/15.62          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 15.37/15.62      inference('cnf', [status(esa)], [t19_xboole_1])).
% 15.37/15.62  thf('56', plain,
% 15.37/15.62      (![X0 : $i, X1 : $i]:
% 15.37/15.62         ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 15.37/15.62           (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X1))
% 15.37/15.62          | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 15.37/15.62               X1))),
% 15.37/15.62      inference('sup-', [status(thm)], ['54', '55'])).
% 15.37/15.62  thf('57', plain,
% 15.37/15.62      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)) @ 
% 15.37/15.62        (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 15.37/15.62         (k2_pre_topc @ sk_A @ sk_C)))),
% 15.37/15.62      inference('sup-', [status(thm)], ['37', '56'])).
% 15.37/15.62  thf('58', plain,
% 15.37/15.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 15.37/15.62      inference('sup+', [status(thm)], ['15', '16'])).
% 15.37/15.62  thf('59', plain,
% 15.37/15.62      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 15.37/15.62        (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 15.37/15.62         (k2_pre_topc @ sk_A @ sk_C)))),
% 15.37/15.62      inference('demod', [status(thm)], ['57', '58'])).
% 15.37/15.62  thf('60', plain, ($false), inference('demod', [status(thm)], ['12', '59'])).
% 15.37/15.62  
% 15.37/15.62  % SZS output end Refutation
% 15.37/15.62  
% 15.37/15.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

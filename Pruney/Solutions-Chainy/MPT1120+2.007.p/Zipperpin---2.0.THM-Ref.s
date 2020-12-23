%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p0mDcJQnZd

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:19 EST 2020

% Result     : Theorem 54.91s
% Output     : Refutation 54.91s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 109 expanded)
%              Number of leaves         :   23 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  672 (1295 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :   15 (   7 average)

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

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
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
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_C )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['17','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( r1_tarski @ X20 @ X22 )
      | ( r1_tarski @ ( k2_pre_topc @ X21 @ X20 ) @ ( k2_pre_topc @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('51',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X1 ) )
      | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['12','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p0mDcJQnZd
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 54.91/55.19  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 54.91/55.19  % Solved by: fo/fo7.sh
% 54.91/55.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 54.91/55.19  % done 33194 iterations in 54.710s
% 54.91/55.19  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 54.91/55.19  % SZS output start Refutation
% 54.91/55.19  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 54.91/55.19  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 54.91/55.19  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 54.91/55.19  thf(sk_B_type, type, sk_B: $i).
% 54.91/55.19  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 54.91/55.19  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 54.91/55.19  thf(sk_A_type, type, sk_A: $i).
% 54.91/55.19  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 54.91/55.19  thf(sk_C_type, type, sk_C: $i).
% 54.91/55.19  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 54.91/55.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 54.91/55.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 54.91/55.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 54.91/55.19  thf(t51_pre_topc, conjecture,
% 54.91/55.19    (![A:$i]:
% 54.91/55.19     ( ( l1_pre_topc @ A ) =>
% 54.91/55.19       ( ![B:$i]:
% 54.91/55.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.91/55.19           ( ![C:$i]:
% 54.91/55.19             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.91/55.19               ( r1_tarski @
% 54.91/55.19                 ( k2_pre_topc @
% 54.91/55.19                   A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 54.91/55.19                 ( k9_subset_1 @
% 54.91/55.19                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 54.91/55.19                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 54.91/55.19  thf(zf_stmt_0, negated_conjecture,
% 54.91/55.19    (~( ![A:$i]:
% 54.91/55.19        ( ( l1_pre_topc @ A ) =>
% 54.91/55.19          ( ![B:$i]:
% 54.91/55.19            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.91/55.19              ( ![C:$i]:
% 54.91/55.19                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.91/55.19                  ( r1_tarski @
% 54.91/55.19                    ( k2_pre_topc @
% 54.91/55.19                      A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 54.91/55.19                    ( k9_subset_1 @
% 54.91/55.19                      ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 54.91/55.19                      ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) )),
% 54.91/55.19    inference('cnf.neg', [status(esa)], [t51_pre_topc])).
% 54.91/55.19  thf('0', plain,
% 54.91/55.19      (~ (r1_tarski @ 
% 54.91/55.19          (k2_pre_topc @ sk_A @ 
% 54.91/55.19           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 54.91/55.19          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 54.91/55.19           (k2_pre_topc @ sk_A @ sk_C)))),
% 54.91/55.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.91/55.19  thf('1', plain,
% 54.91/55.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.91/55.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.91/55.19  thf(redefinition_k9_subset_1, axiom,
% 54.91/55.19    (![A:$i,B:$i,C:$i]:
% 54.91/55.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 54.91/55.19       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 54.91/55.19  thf('2', plain,
% 54.91/55.19      (![X10 : $i, X11 : $i, X12 : $i]:
% 54.91/55.19         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 54.91/55.19          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 54.91/55.19      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 54.91/55.19  thf('3', plain,
% 54.91/55.19      (![X0 : $i]:
% 54.91/55.19         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 54.91/55.19           = (k3_xboole_0 @ X0 @ sk_C))),
% 54.91/55.19      inference('sup-', [status(thm)], ['1', '2'])).
% 54.91/55.19  thf('4', plain,
% 54.91/55.19      (~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 54.91/55.19          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 54.91/55.19           (k2_pre_topc @ sk_A @ sk_C)))),
% 54.91/55.19      inference('demod', [status(thm)], ['0', '3'])).
% 54.91/55.19  thf('5', plain,
% 54.91/55.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.91/55.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.91/55.19  thf(dt_k2_pre_topc, axiom,
% 54.91/55.19    (![A:$i,B:$i]:
% 54.91/55.19     ( ( ( l1_pre_topc @ A ) & 
% 54.91/55.19         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 54.91/55.19       ( m1_subset_1 @
% 54.91/55.19         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 54.91/55.19  thf('6', plain,
% 54.91/55.19      (![X18 : $i, X19 : $i]:
% 54.91/55.19         (~ (l1_pre_topc @ X18)
% 54.91/55.19          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 54.91/55.19          | (m1_subset_1 @ (k2_pre_topc @ X18 @ X19) @ 
% 54.91/55.19             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 54.91/55.19      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 54.91/55.19  thf('7', plain,
% 54.91/55.19      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 54.91/55.19         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.91/55.19        | ~ (l1_pre_topc @ sk_A))),
% 54.91/55.19      inference('sup-', [status(thm)], ['5', '6'])).
% 54.91/55.19  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 54.91/55.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.91/55.19  thf('9', plain,
% 54.91/55.19      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 54.91/55.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.91/55.19      inference('demod', [status(thm)], ['7', '8'])).
% 54.91/55.19  thf('10', plain,
% 54.91/55.19      (![X10 : $i, X11 : $i, X12 : $i]:
% 54.91/55.19         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 54.91/55.19          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 54.91/55.19      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 54.91/55.19  thf('11', plain,
% 54.91/55.19      (![X0 : $i]:
% 54.91/55.19         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 54.91/55.19           (k2_pre_topc @ sk_A @ sk_C))
% 54.91/55.19           = (k3_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ sk_C)))),
% 54.91/55.19      inference('sup-', [status(thm)], ['9', '10'])).
% 54.91/55.19  thf('12', plain,
% 54.91/55.19      (~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 54.91/55.19          (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 54.91/55.19           (k2_pre_topc @ sk_A @ sk_C)))),
% 54.91/55.19      inference('demod', [status(thm)], ['4', '11'])).
% 54.91/55.19  thf(commutativity_k2_tarski, axiom,
% 54.91/55.19    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 54.91/55.19  thf('13', plain,
% 54.91/55.19      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 54.91/55.19      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 54.91/55.19  thf(t12_setfam_1, axiom,
% 54.91/55.19    (![A:$i,B:$i]:
% 54.91/55.19     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 54.91/55.19  thf('14', plain,
% 54.91/55.19      (![X13 : $i, X14 : $i]:
% 54.91/55.19         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 54.91/55.19      inference('cnf', [status(esa)], [t12_setfam_1])).
% 54.91/55.19  thf('15', plain,
% 54.91/55.19      (![X0 : $i, X1 : $i]:
% 54.91/55.19         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 54.91/55.19      inference('sup+', [status(thm)], ['13', '14'])).
% 54.91/55.19  thf('16', plain,
% 54.91/55.19      (![X13 : $i, X14 : $i]:
% 54.91/55.19         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 54.91/55.19      inference('cnf', [status(esa)], [t12_setfam_1])).
% 54.91/55.19  thf('17', plain,
% 54.91/55.19      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 54.91/55.19      inference('sup+', [status(thm)], ['15', '16'])).
% 54.91/55.19  thf('18', plain,
% 54.91/55.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.91/55.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.91/55.19  thf('19', plain,
% 54.91/55.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.91/55.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.91/55.19  thf(t3_subset, axiom,
% 54.91/55.19    (![A:$i,B:$i]:
% 54.91/55.19     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 54.91/55.19  thf('20', plain,
% 54.91/55.19      (![X15 : $i, X16 : $i]:
% 54.91/55.19         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 54.91/55.19      inference('cnf', [status(esa)], [t3_subset])).
% 54.91/55.19  thf('21', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 54.91/55.19      inference('sup-', [status(thm)], ['19', '20'])).
% 54.91/55.19  thf(t17_xboole_1, axiom,
% 54.91/55.19    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 54.91/55.19  thf('22', plain,
% 54.91/55.19      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 54.91/55.19      inference('cnf', [status(esa)], [t17_xboole_1])).
% 54.91/55.19  thf(t1_xboole_1, axiom,
% 54.91/55.19    (![A:$i,B:$i,C:$i]:
% 54.91/55.19     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 54.91/55.19       ( r1_tarski @ A @ C ) ))).
% 54.91/55.19  thf('23', plain,
% 54.91/55.19      (![X5 : $i, X6 : $i, X7 : $i]:
% 54.91/55.19         (~ (r1_tarski @ X5 @ X6)
% 54.91/55.19          | ~ (r1_tarski @ X6 @ X7)
% 54.91/55.19          | (r1_tarski @ X5 @ X7))),
% 54.91/55.19      inference('cnf', [status(esa)], [t1_xboole_1])).
% 54.91/55.19  thf('24', plain,
% 54.91/55.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.91/55.19         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 54.91/55.19      inference('sup-', [status(thm)], ['22', '23'])).
% 54.91/55.19  thf('25', plain,
% 54.91/55.19      (![X0 : $i]:
% 54.91/55.19         (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ (u1_struct_0 @ sk_A))),
% 54.91/55.19      inference('sup-', [status(thm)], ['21', '24'])).
% 54.91/55.19  thf('26', plain,
% 54.91/55.19      (![X15 : $i, X17 : $i]:
% 54.91/55.19         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 54.91/55.19      inference('cnf', [status(esa)], [t3_subset])).
% 54.91/55.19  thf('27', plain,
% 54.91/55.19      (![X0 : $i]:
% 54.91/55.19         (m1_subset_1 @ (k3_xboole_0 @ sk_C @ X0) @ 
% 54.91/55.19          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.91/55.19      inference('sup-', [status(thm)], ['25', '26'])).
% 54.91/55.19  thf(t49_pre_topc, axiom,
% 54.91/55.19    (![A:$i]:
% 54.91/55.19     ( ( l1_pre_topc @ A ) =>
% 54.91/55.19       ( ![B:$i]:
% 54.91/55.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.91/55.19           ( ![C:$i]:
% 54.91/55.19             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.91/55.19               ( ( r1_tarski @ B @ C ) =>
% 54.91/55.19                 ( r1_tarski @
% 54.91/55.19                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 54.91/55.19  thf('28', plain,
% 54.91/55.19      (![X20 : $i, X21 : $i, X22 : $i]:
% 54.91/55.19         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 54.91/55.19          | ~ (r1_tarski @ X20 @ X22)
% 54.91/55.19          | (r1_tarski @ (k2_pre_topc @ X21 @ X20) @ (k2_pre_topc @ X21 @ X22))
% 54.91/55.19          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 54.91/55.19          | ~ (l1_pre_topc @ X21))),
% 54.91/55.19      inference('cnf', [status(esa)], [t49_pre_topc])).
% 54.91/55.19  thf('29', plain,
% 54.91/55.19      (![X0 : $i, X1 : $i]:
% 54.91/55.19         (~ (l1_pre_topc @ sk_A)
% 54.91/55.19          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.91/55.19          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0)) @ 
% 54.91/55.19             (k2_pre_topc @ sk_A @ X1))
% 54.91/55.19          | ~ (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ X1))),
% 54.91/55.19      inference('sup-', [status(thm)], ['27', '28'])).
% 54.91/55.19  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 54.91/55.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.91/55.19  thf('31', plain,
% 54.91/55.19      (![X0 : $i, X1 : $i]:
% 54.91/55.19         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.91/55.19          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0)) @ 
% 54.91/55.19             (k2_pre_topc @ sk_A @ X1))
% 54.91/55.19          | ~ (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ X1))),
% 54.91/55.19      inference('demod', [status(thm)], ['29', '30'])).
% 54.91/55.19  thf('32', plain,
% 54.91/55.19      (![X0 : $i]:
% 54.91/55.19         (~ (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ sk_C)
% 54.91/55.19          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0)) @ 
% 54.91/55.19             (k2_pre_topc @ sk_A @ sk_C)))),
% 54.91/55.19      inference('sup-', [status(thm)], ['18', '31'])).
% 54.91/55.19  thf('33', plain,
% 54.91/55.19      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 54.91/55.19      inference('cnf', [status(esa)], [t17_xboole_1])).
% 54.91/55.19  thf('34', plain,
% 54.91/55.19      (![X0 : $i]:
% 54.91/55.19         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0)) @ 
% 54.91/55.19          (k2_pre_topc @ sk_A @ sk_C))),
% 54.91/55.19      inference('demod', [status(thm)], ['32', '33'])).
% 54.91/55.19  thf('35', plain,
% 54.91/55.19      (![X0 : $i]:
% 54.91/55.19         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 54.91/55.19          (k2_pre_topc @ sk_A @ sk_C))),
% 54.91/55.19      inference('sup+', [status(thm)], ['17', '34'])).
% 54.91/55.19  thf('36', plain,
% 54.91/55.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.91/55.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.91/55.19  thf('37', plain,
% 54.91/55.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.91/55.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.91/55.19  thf('38', plain,
% 54.91/55.19      (![X15 : $i, X16 : $i]:
% 54.91/55.19         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 54.91/55.19      inference('cnf', [status(esa)], [t3_subset])).
% 54.91/55.19  thf('39', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 54.91/55.19      inference('sup-', [status(thm)], ['37', '38'])).
% 54.91/55.19  thf('40', plain,
% 54.91/55.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.91/55.19         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 54.91/55.19      inference('sup-', [status(thm)], ['22', '23'])).
% 54.91/55.19  thf('41', plain,
% 54.91/55.19      (![X0 : $i]:
% 54.91/55.19         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 54.91/55.19      inference('sup-', [status(thm)], ['39', '40'])).
% 54.91/55.19  thf('42', plain,
% 54.91/55.19      (![X15 : $i, X17 : $i]:
% 54.91/55.19         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 54.91/55.19      inference('cnf', [status(esa)], [t3_subset])).
% 54.91/55.19  thf('43', plain,
% 54.91/55.19      (![X0 : $i]:
% 54.91/55.19         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 54.91/55.19          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.91/55.19      inference('sup-', [status(thm)], ['41', '42'])).
% 54.91/55.19  thf('44', plain,
% 54.91/55.19      (![X20 : $i, X21 : $i, X22 : $i]:
% 54.91/55.19         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 54.91/55.19          | ~ (r1_tarski @ X20 @ X22)
% 54.91/55.19          | (r1_tarski @ (k2_pre_topc @ X21 @ X20) @ (k2_pre_topc @ X21 @ X22))
% 54.91/55.19          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 54.91/55.19          | ~ (l1_pre_topc @ X21))),
% 54.91/55.19      inference('cnf', [status(esa)], [t49_pre_topc])).
% 54.91/55.19  thf('45', plain,
% 54.91/55.19      (![X0 : $i, X1 : $i]:
% 54.91/55.19         (~ (l1_pre_topc @ sk_A)
% 54.91/55.19          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.91/55.19          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 54.91/55.19             (k2_pre_topc @ sk_A @ X1))
% 54.91/55.19          | ~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ X1))),
% 54.91/55.19      inference('sup-', [status(thm)], ['43', '44'])).
% 54.91/55.19  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 54.91/55.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.91/55.19  thf('47', plain,
% 54.91/55.19      (![X0 : $i, X1 : $i]:
% 54.91/55.19         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.91/55.19          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 54.91/55.19             (k2_pre_topc @ sk_A @ X1))
% 54.91/55.19          | ~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ X1))),
% 54.91/55.19      inference('demod', [status(thm)], ['45', '46'])).
% 54.91/55.19  thf('48', plain,
% 54.91/55.19      (![X0 : $i]:
% 54.91/55.19         (~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)
% 54.91/55.19          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 54.91/55.19             (k2_pre_topc @ sk_A @ sk_B)))),
% 54.91/55.19      inference('sup-', [status(thm)], ['36', '47'])).
% 54.91/55.19  thf('49', plain,
% 54.91/55.19      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 54.91/55.19      inference('cnf', [status(esa)], [t17_xboole_1])).
% 54.91/55.19  thf('50', plain,
% 54.91/55.19      (![X0 : $i]:
% 54.91/55.19         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 54.91/55.19          (k2_pre_topc @ sk_A @ sk_B))),
% 54.91/55.19      inference('demod', [status(thm)], ['48', '49'])).
% 54.91/55.19  thf(t19_xboole_1, axiom,
% 54.91/55.19    (![A:$i,B:$i,C:$i]:
% 54.91/55.19     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 54.91/55.19       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 54.91/55.19  thf('51', plain,
% 54.91/55.19      (![X2 : $i, X3 : $i, X4 : $i]:
% 54.91/55.19         (~ (r1_tarski @ X2 @ X3)
% 54.91/55.19          | ~ (r1_tarski @ X2 @ X4)
% 54.91/55.19          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 54.91/55.19      inference('cnf', [status(esa)], [t19_xboole_1])).
% 54.91/55.19  thf('52', plain,
% 54.91/55.19      (![X0 : $i, X1 : $i]:
% 54.91/55.19         ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 54.91/55.19           (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X1))
% 54.91/55.19          | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 54.91/55.19               X1))),
% 54.91/55.19      inference('sup-', [status(thm)], ['50', '51'])).
% 54.91/55.19  thf('53', plain,
% 54.91/55.19      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 54.91/55.19        (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 54.91/55.19         (k2_pre_topc @ sk_A @ sk_C)))),
% 54.91/55.19      inference('sup-', [status(thm)], ['35', '52'])).
% 54.91/55.19  thf('54', plain, ($false), inference('demod', [status(thm)], ['12', '53'])).
% 54.91/55.19  
% 54.91/55.19  % SZS output end Refutation
% 54.91/55.19  
% 55.02/55.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.woALLjpKjm

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:19 EST 2020

% Result     : Theorem 36.35s
% Output     : Refutation 36.35s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 169 expanded)
%              Number of leaves         :   20 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :  782 (1767 expanded)
%              Number of equality atoms :   12 (  32 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ sk_C ) )
      = ( k3_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k3_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X9 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('25',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['23','26'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X8 )
      | ( r1_tarski @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','29'])).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','29'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k3_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('43',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( r1_tarski @ X22 @ X24 )
      | ( r1_tarski @ ( k2_pre_topc @ X23 @ X22 ) @ ( k2_pre_topc @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_C )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['35','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['34','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k3_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( r1_tarski @ X22 @ X24 )
      | ( r1_tarski @ ( k2_pre_topc @ X23 @ X22 ) @ ( k2_pre_topc @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['51','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X8 )
      | ( r1_tarski @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X1 ) )
      | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['12','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.woALLjpKjm
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:04:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 36.35/36.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 36.35/36.56  % Solved by: fo/fo7.sh
% 36.35/36.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 36.35/36.56  % done 30609 iterations in 36.123s
% 36.35/36.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 36.35/36.56  % SZS output start Refutation
% 36.35/36.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 36.35/36.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 36.35/36.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 36.35/36.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 36.35/36.56  thf(sk_C_type, type, sk_C: $i).
% 36.35/36.56  thf(sk_A_type, type, sk_A: $i).
% 36.35/36.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 36.35/36.56  thf(sk_B_type, type, sk_B: $i).
% 36.35/36.56  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 36.35/36.56  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 36.35/36.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 36.35/36.56  thf(t51_pre_topc, conjecture,
% 36.35/36.56    (![A:$i]:
% 36.35/36.56     ( ( l1_pre_topc @ A ) =>
% 36.35/36.56       ( ![B:$i]:
% 36.35/36.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 36.35/36.56           ( ![C:$i]:
% 36.35/36.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 36.35/36.56               ( r1_tarski @
% 36.35/36.56                 ( k2_pre_topc @
% 36.35/36.56                   A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 36.35/36.56                 ( k9_subset_1 @
% 36.35/36.56                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 36.35/36.56                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 36.35/36.56  thf(zf_stmt_0, negated_conjecture,
% 36.35/36.56    (~( ![A:$i]:
% 36.35/36.56        ( ( l1_pre_topc @ A ) =>
% 36.35/36.56          ( ![B:$i]:
% 36.35/36.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 36.35/36.56              ( ![C:$i]:
% 36.35/36.56                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 36.35/36.56                  ( r1_tarski @
% 36.35/36.56                    ( k2_pre_topc @
% 36.35/36.56                      A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 36.35/36.56                    ( k9_subset_1 @
% 36.35/36.56                      ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 36.35/36.56                      ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) )),
% 36.35/36.56    inference('cnf.neg', [status(esa)], [t51_pre_topc])).
% 36.35/36.56  thf('0', plain,
% 36.35/36.56      (~ (r1_tarski @ 
% 36.35/36.56          (k2_pre_topc @ sk_A @ 
% 36.35/36.56           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 36.35/36.56          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 36.35/36.56           (k2_pre_topc @ sk_A @ sk_C)))),
% 36.35/36.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.35/36.56  thf('1', plain,
% 36.35/36.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 36.35/36.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.35/36.56  thf(redefinition_k9_subset_1, axiom,
% 36.35/36.56    (![A:$i,B:$i,C:$i]:
% 36.35/36.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 36.35/36.56       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 36.35/36.56  thf('2', plain,
% 36.35/36.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 36.35/36.56         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 36.35/36.56          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 36.35/36.56      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 36.35/36.56  thf('3', plain,
% 36.35/36.56      (![X0 : $i]:
% 36.35/36.56         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 36.35/36.56           = (k3_xboole_0 @ X0 @ sk_C))),
% 36.35/36.56      inference('sup-', [status(thm)], ['1', '2'])).
% 36.35/36.56  thf('4', plain,
% 36.35/36.56      (~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 36.35/36.56          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 36.35/36.56           (k2_pre_topc @ sk_A @ sk_C)))),
% 36.35/36.56      inference('demod', [status(thm)], ['0', '3'])).
% 36.35/36.56  thf('5', plain,
% 36.35/36.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 36.35/36.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.35/36.56  thf(dt_k2_pre_topc, axiom,
% 36.35/36.56    (![A:$i,B:$i]:
% 36.35/36.56     ( ( ( l1_pre_topc @ A ) & 
% 36.35/36.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 36.35/36.56       ( m1_subset_1 @
% 36.35/36.56         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 36.35/36.56  thf('6', plain,
% 36.35/36.56      (![X20 : $i, X21 : $i]:
% 36.35/36.56         (~ (l1_pre_topc @ X20)
% 36.35/36.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 36.35/36.56          | (m1_subset_1 @ (k2_pre_topc @ X20 @ X21) @ 
% 36.35/36.56             (k1_zfmisc_1 @ (u1_struct_0 @ X20))))),
% 36.35/36.56      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 36.35/36.56  thf('7', plain,
% 36.35/36.56      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 36.35/36.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 36.35/36.56        | ~ (l1_pre_topc @ sk_A))),
% 36.35/36.56      inference('sup-', [status(thm)], ['5', '6'])).
% 36.35/36.56  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 36.35/36.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.35/36.56  thf('9', plain,
% 36.35/36.56      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 36.35/36.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 36.35/36.56      inference('demod', [status(thm)], ['7', '8'])).
% 36.35/36.56  thf('10', plain,
% 36.35/36.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 36.35/36.56         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 36.35/36.56          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 36.35/36.56      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 36.35/36.56  thf('11', plain,
% 36.35/36.56      (![X0 : $i]:
% 36.35/36.56         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 36.35/36.56           (k2_pre_topc @ sk_A @ sk_C))
% 36.35/36.56           = (k3_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ sk_C)))),
% 36.35/36.56      inference('sup-', [status(thm)], ['9', '10'])).
% 36.35/36.56  thf('12', plain,
% 36.35/36.56      (~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 36.35/36.56          (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 36.35/36.56           (k2_pre_topc @ sk_A @ sk_C)))),
% 36.35/36.56      inference('demod', [status(thm)], ['4', '11'])).
% 36.35/36.56  thf(d10_xboole_0, axiom,
% 36.35/36.56    (![A:$i,B:$i]:
% 36.35/36.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 36.35/36.56  thf('13', plain,
% 36.35/36.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 36.35/36.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 36.35/36.56  thf('14', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 36.35/36.56      inference('simplify', [status(thm)], ['13'])).
% 36.35/36.56  thf(t108_xboole_1, axiom,
% 36.35/36.56    (![A:$i,B:$i,C:$i]:
% 36.35/36.56     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 36.35/36.56  thf('15', plain,
% 36.35/36.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 36.35/36.56         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ (k3_xboole_0 @ X3 @ X5) @ X4))),
% 36.35/36.56      inference('cnf', [status(esa)], [t108_xboole_1])).
% 36.35/36.56  thf('16', plain,
% 36.35/36.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 36.35/36.56      inference('sup-', [status(thm)], ['14', '15'])).
% 36.35/36.56  thf('17', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 36.35/36.56      inference('simplify', [status(thm)], ['13'])).
% 36.35/36.56  thf(t3_subset, axiom,
% 36.35/36.56    (![A:$i,B:$i]:
% 36.35/36.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 36.35/36.56  thf('18', plain,
% 36.35/36.56      (![X17 : $i, X19 : $i]:
% 36.35/36.56         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 36.35/36.56      inference('cnf', [status(esa)], [t3_subset])).
% 36.35/36.56  thf('19', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 36.35/36.56      inference('sup-', [status(thm)], ['17', '18'])).
% 36.35/36.56  thf(dt_k9_subset_1, axiom,
% 36.35/36.56    (![A:$i,B:$i,C:$i]:
% 36.35/36.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 36.35/36.56       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 36.35/36.56  thf('20', plain,
% 36.35/36.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 36.35/36.56         ((m1_subset_1 @ (k9_subset_1 @ X9 @ X10 @ X11) @ (k1_zfmisc_1 @ X9))
% 36.35/36.56          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X9)))),
% 36.35/36.56      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 36.35/36.56  thf('21', plain,
% 36.35/36.56      (![X0 : $i, X1 : $i]:
% 36.35/36.56         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 36.35/36.56      inference('sup-', [status(thm)], ['19', '20'])).
% 36.35/36.56  thf('22', plain,
% 36.35/36.56      (![X17 : $i, X18 : $i]:
% 36.35/36.56         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 36.35/36.56      inference('cnf', [status(esa)], [t3_subset])).
% 36.35/36.56  thf('23', plain,
% 36.35/36.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 36.35/36.56      inference('sup-', [status(thm)], ['21', '22'])).
% 36.35/36.56  thf('24', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 36.35/36.56      inference('sup-', [status(thm)], ['17', '18'])).
% 36.35/36.56  thf('25', plain,
% 36.35/36.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 36.35/36.56         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 36.35/36.56          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 36.35/36.56      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 36.35/36.56  thf('26', plain,
% 36.35/36.56      (![X0 : $i, X1 : $i]:
% 36.35/36.56         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 36.35/36.56      inference('sup-', [status(thm)], ['24', '25'])).
% 36.35/36.56  thf('27', plain,
% 36.35/36.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 36.35/36.56      inference('demod', [status(thm)], ['23', '26'])).
% 36.35/36.56  thf(t19_xboole_1, axiom,
% 36.35/36.56    (![A:$i,B:$i,C:$i]:
% 36.35/36.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 36.35/36.56       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 36.35/36.56  thf('28', plain,
% 36.35/36.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 36.35/36.56         (~ (r1_tarski @ X6 @ X7)
% 36.35/36.56          | ~ (r1_tarski @ X6 @ X8)
% 36.35/36.56          | (r1_tarski @ X6 @ (k3_xboole_0 @ X7 @ X8)))),
% 36.35/36.56      inference('cnf', [status(esa)], [t19_xboole_1])).
% 36.35/36.56  thf('29', plain,
% 36.35/36.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.35/36.56         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X2))
% 36.35/36.56          | ~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 36.35/36.56      inference('sup-', [status(thm)], ['27', '28'])).
% 36.35/36.56  thf('30', plain,
% 36.35/36.56      (![X0 : $i, X1 : $i]:
% 36.35/36.56         (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))),
% 36.35/36.56      inference('sup-', [status(thm)], ['16', '29'])).
% 36.35/36.56  thf('31', plain,
% 36.35/36.56      (![X0 : $i, X2 : $i]:
% 36.35/36.56         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 36.35/36.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 36.35/36.56  thf('32', plain,
% 36.35/36.56      (![X0 : $i, X1 : $i]:
% 36.35/36.56         (~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 36.35/36.56          | ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1)))),
% 36.35/36.56      inference('sup-', [status(thm)], ['30', '31'])).
% 36.35/36.56  thf('33', plain,
% 36.35/36.56      (![X0 : $i, X1 : $i]:
% 36.35/36.56         (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))),
% 36.35/36.56      inference('sup-', [status(thm)], ['16', '29'])).
% 36.35/36.56  thf('34', plain,
% 36.35/36.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 36.35/36.56      inference('demod', [status(thm)], ['32', '33'])).
% 36.35/36.56  thf('35', plain,
% 36.35/36.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 36.35/36.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.35/36.56  thf('36', plain,
% 36.35/36.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 36.35/36.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.35/36.56  thf('37', plain,
% 36.35/36.56      (![X17 : $i, X18 : $i]:
% 36.35/36.56         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 36.35/36.56      inference('cnf', [status(esa)], [t3_subset])).
% 36.35/36.56  thf('38', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 36.35/36.56      inference('sup-', [status(thm)], ['36', '37'])).
% 36.35/36.56  thf('39', plain,
% 36.35/36.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 36.35/36.56         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ (k3_xboole_0 @ X3 @ X5) @ X4))),
% 36.35/36.56      inference('cnf', [status(esa)], [t108_xboole_1])).
% 36.35/36.56  thf('40', plain,
% 36.35/36.56      (![X0 : $i]:
% 36.35/36.56         (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ (u1_struct_0 @ sk_A))),
% 36.35/36.56      inference('sup-', [status(thm)], ['38', '39'])).
% 36.35/36.56  thf('41', plain,
% 36.35/36.56      (![X17 : $i, X19 : $i]:
% 36.35/36.56         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 36.35/36.56      inference('cnf', [status(esa)], [t3_subset])).
% 36.35/36.56  thf('42', plain,
% 36.35/36.56      (![X0 : $i]:
% 36.35/36.56         (m1_subset_1 @ (k3_xboole_0 @ sk_C @ X0) @ 
% 36.35/36.56          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 36.35/36.56      inference('sup-', [status(thm)], ['40', '41'])).
% 36.35/36.56  thf(t49_pre_topc, axiom,
% 36.35/36.56    (![A:$i]:
% 36.35/36.56     ( ( l1_pre_topc @ A ) =>
% 36.35/36.56       ( ![B:$i]:
% 36.35/36.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 36.35/36.56           ( ![C:$i]:
% 36.35/36.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 36.35/36.56               ( ( r1_tarski @ B @ C ) =>
% 36.35/36.56                 ( r1_tarski @
% 36.35/36.56                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 36.35/36.56  thf('43', plain,
% 36.35/36.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 36.35/36.56         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 36.35/36.56          | ~ (r1_tarski @ X22 @ X24)
% 36.35/36.56          | (r1_tarski @ (k2_pre_topc @ X23 @ X22) @ (k2_pre_topc @ X23 @ X24))
% 36.35/36.56          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 36.35/36.56          | ~ (l1_pre_topc @ X23))),
% 36.35/36.56      inference('cnf', [status(esa)], [t49_pre_topc])).
% 36.35/36.56  thf('44', plain,
% 36.35/36.56      (![X0 : $i, X1 : $i]:
% 36.35/36.56         (~ (l1_pre_topc @ sk_A)
% 36.35/36.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 36.35/36.56          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0)) @ 
% 36.35/36.56             (k2_pre_topc @ sk_A @ X1))
% 36.35/36.56          | ~ (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ X1))),
% 36.35/36.56      inference('sup-', [status(thm)], ['42', '43'])).
% 36.35/36.56  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 36.35/36.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.35/36.56  thf('46', plain,
% 36.35/36.56      (![X0 : $i, X1 : $i]:
% 36.35/36.56         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 36.35/36.56          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0)) @ 
% 36.35/36.56             (k2_pre_topc @ sk_A @ X1))
% 36.35/36.56          | ~ (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ X1))),
% 36.35/36.56      inference('demod', [status(thm)], ['44', '45'])).
% 36.35/36.56  thf('47', plain,
% 36.35/36.56      (![X0 : $i]:
% 36.35/36.56         (~ (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ sk_C)
% 36.35/36.56          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0)) @ 
% 36.35/36.56             (k2_pre_topc @ sk_A @ sk_C)))),
% 36.35/36.56      inference('sup-', [status(thm)], ['35', '46'])).
% 36.35/36.56  thf('48', plain,
% 36.35/36.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 36.35/36.56      inference('sup-', [status(thm)], ['14', '15'])).
% 36.35/36.56  thf('49', plain,
% 36.35/36.56      (![X0 : $i]:
% 36.35/36.56         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0)) @ 
% 36.35/36.56          (k2_pre_topc @ sk_A @ sk_C))),
% 36.35/36.56      inference('demod', [status(thm)], ['47', '48'])).
% 36.35/36.56  thf('50', plain,
% 36.35/36.56      (![X0 : $i]:
% 36.35/36.56         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 36.35/36.56          (k2_pre_topc @ sk_A @ sk_C))),
% 36.35/36.56      inference('sup+', [status(thm)], ['34', '49'])).
% 36.35/36.56  thf('51', plain,
% 36.35/36.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 36.35/36.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.35/36.56  thf('52', plain,
% 36.35/36.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 36.35/36.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.35/36.56  thf('53', plain,
% 36.35/36.56      (![X17 : $i, X18 : $i]:
% 36.35/36.56         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 36.35/36.56      inference('cnf', [status(esa)], [t3_subset])).
% 36.35/36.56  thf('54', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.35/36.56      inference('sup-', [status(thm)], ['52', '53'])).
% 36.35/36.56  thf('55', plain,
% 36.35/36.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 36.35/36.56         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ (k3_xboole_0 @ X3 @ X5) @ X4))),
% 36.35/36.56      inference('cnf', [status(esa)], [t108_xboole_1])).
% 36.35/36.56  thf('56', plain,
% 36.35/36.56      (![X0 : $i]:
% 36.35/36.56         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 36.35/36.56      inference('sup-', [status(thm)], ['54', '55'])).
% 36.35/36.56  thf('57', plain,
% 36.35/36.56      (![X17 : $i, X19 : $i]:
% 36.35/36.56         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 36.35/36.56      inference('cnf', [status(esa)], [t3_subset])).
% 36.35/36.56  thf('58', plain,
% 36.35/36.56      (![X0 : $i]:
% 36.35/36.56         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 36.35/36.56          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 36.35/36.56      inference('sup-', [status(thm)], ['56', '57'])).
% 36.35/36.56  thf('59', plain,
% 36.35/36.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 36.35/36.56         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 36.35/36.56          | ~ (r1_tarski @ X22 @ X24)
% 36.35/36.56          | (r1_tarski @ (k2_pre_topc @ X23 @ X22) @ (k2_pre_topc @ X23 @ X24))
% 36.35/36.56          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 36.35/36.56          | ~ (l1_pre_topc @ X23))),
% 36.35/36.56      inference('cnf', [status(esa)], [t49_pre_topc])).
% 36.35/36.56  thf('60', plain,
% 36.35/36.56      (![X0 : $i, X1 : $i]:
% 36.35/36.56         (~ (l1_pre_topc @ sk_A)
% 36.35/36.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 36.35/36.56          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 36.35/36.56             (k2_pre_topc @ sk_A @ X1))
% 36.35/36.56          | ~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ X1))),
% 36.35/36.56      inference('sup-', [status(thm)], ['58', '59'])).
% 36.35/36.56  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 36.35/36.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.35/36.56  thf('62', plain,
% 36.35/36.56      (![X0 : $i, X1 : $i]:
% 36.35/36.56         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 36.35/36.56          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 36.35/36.56             (k2_pre_topc @ sk_A @ X1))
% 36.35/36.56          | ~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ X1))),
% 36.35/36.56      inference('demod', [status(thm)], ['60', '61'])).
% 36.35/36.56  thf('63', plain,
% 36.35/36.56      (![X0 : $i]:
% 36.35/36.56         (~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)
% 36.35/36.56          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 36.35/36.56             (k2_pre_topc @ sk_A @ sk_B)))),
% 36.35/36.56      inference('sup-', [status(thm)], ['51', '62'])).
% 36.35/36.56  thf('64', plain,
% 36.35/36.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 36.35/36.56      inference('sup-', [status(thm)], ['14', '15'])).
% 36.35/36.56  thf('65', plain,
% 36.35/36.56      (![X0 : $i]:
% 36.35/36.56         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 36.35/36.56          (k2_pre_topc @ sk_A @ sk_B))),
% 36.35/36.56      inference('demod', [status(thm)], ['63', '64'])).
% 36.35/36.56  thf('66', plain,
% 36.35/36.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 36.35/36.56         (~ (r1_tarski @ X6 @ X7)
% 36.35/36.56          | ~ (r1_tarski @ X6 @ X8)
% 36.35/36.56          | (r1_tarski @ X6 @ (k3_xboole_0 @ X7 @ X8)))),
% 36.35/36.56      inference('cnf', [status(esa)], [t19_xboole_1])).
% 36.35/36.56  thf('67', plain,
% 36.35/36.56      (![X0 : $i, X1 : $i]:
% 36.35/36.56         ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 36.35/36.56           (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X1))
% 36.35/36.56          | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 36.35/36.56               X1))),
% 36.35/36.56      inference('sup-', [status(thm)], ['65', '66'])).
% 36.35/36.56  thf('68', plain,
% 36.35/36.56      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 36.35/36.56        (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 36.35/36.56         (k2_pre_topc @ sk_A @ sk_C)))),
% 36.35/36.56      inference('sup-', [status(thm)], ['50', '67'])).
% 36.35/36.56  thf('69', plain, ($false), inference('demod', [status(thm)], ['12', '68'])).
% 36.35/36.56  
% 36.35/36.56  % SZS output end Refutation
% 36.35/36.56  
% 36.35/36.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

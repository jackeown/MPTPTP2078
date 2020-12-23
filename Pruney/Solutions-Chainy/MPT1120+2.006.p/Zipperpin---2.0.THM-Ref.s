%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o7sLeReFAg

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:19 EST 2020

% Result     : Theorem 48.61s
% Output     : Refutation 48.61s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 116 expanded)
%              Number of leaves         :   25 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  693 (1337 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( r1_tarski @ X22 @ X24 )
      | ( r1_tarski @ ( k2_pre_topc @ X23 @ X22 ) @ ( k2_pre_topc @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_C )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['18','33'])).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['17','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( r1_tarski @ X22 @ X24 )
      | ( r1_tarski @ ( k2_pre_topc @ X23 @ X22 ) @ ( k2_pre_topc @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','49'])).

thf('51',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('53',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ( r1_tarski @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X1 ) )
      | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['12','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o7sLeReFAg
% 0.13/0.37  % Computer   : n011.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 14:53:12 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 48.61/48.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 48.61/48.84  % Solved by: fo/fo7.sh
% 48.61/48.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 48.61/48.84  % done 26885 iterations in 48.360s
% 48.61/48.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 48.61/48.84  % SZS output start Refutation
% 48.61/48.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 48.61/48.84  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 48.61/48.84  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 48.61/48.84  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 48.61/48.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 48.61/48.84  thf(sk_C_type, type, sk_C: $i).
% 48.61/48.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 48.61/48.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 48.61/48.84  thf(sk_A_type, type, sk_A: $i).
% 48.61/48.84  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 48.61/48.84  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 48.61/48.84  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 48.61/48.84  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 48.61/48.84  thf(sk_B_type, type, sk_B: $i).
% 48.61/48.84  thf(t51_pre_topc, conjecture,
% 48.61/48.84    (![A:$i]:
% 48.61/48.84     ( ( l1_pre_topc @ A ) =>
% 48.61/48.84       ( ![B:$i]:
% 48.61/48.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 48.61/48.84           ( ![C:$i]:
% 48.61/48.84             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 48.61/48.84               ( r1_tarski @
% 48.61/48.84                 ( k2_pre_topc @
% 48.61/48.84                   A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 48.61/48.84                 ( k9_subset_1 @
% 48.61/48.84                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 48.61/48.84                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 48.61/48.84  thf(zf_stmt_0, negated_conjecture,
% 48.61/48.84    (~( ![A:$i]:
% 48.61/48.84        ( ( l1_pre_topc @ A ) =>
% 48.61/48.84          ( ![B:$i]:
% 48.61/48.84            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 48.61/48.84              ( ![C:$i]:
% 48.61/48.84                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 48.61/48.84                  ( r1_tarski @
% 48.61/48.84                    ( k2_pre_topc @
% 48.61/48.84                      A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 48.61/48.84                    ( k9_subset_1 @
% 48.61/48.84                      ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 48.61/48.84                      ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) )),
% 48.61/48.84    inference('cnf.neg', [status(esa)], [t51_pre_topc])).
% 48.61/48.84  thf('0', plain,
% 48.61/48.84      (~ (r1_tarski @ 
% 48.61/48.84          (k2_pre_topc @ sk_A @ 
% 48.61/48.84           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 48.61/48.84          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 48.61/48.84           (k2_pre_topc @ sk_A @ sk_C)))),
% 48.61/48.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.61/48.84  thf('1', plain,
% 48.61/48.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 48.61/48.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.61/48.84  thf(redefinition_k9_subset_1, axiom,
% 48.61/48.84    (![A:$i,B:$i,C:$i]:
% 48.61/48.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 48.61/48.84       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 48.61/48.84  thf('2', plain,
% 48.61/48.84      (![X12 : $i, X13 : $i, X14 : $i]:
% 48.61/48.84         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 48.61/48.84          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 48.61/48.84      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 48.61/48.84  thf('3', plain,
% 48.61/48.84      (![X0 : $i]:
% 48.61/48.84         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 48.61/48.84           = (k3_xboole_0 @ X0 @ sk_C))),
% 48.61/48.84      inference('sup-', [status(thm)], ['1', '2'])).
% 48.61/48.84  thf('4', plain,
% 48.61/48.84      (~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 48.61/48.84          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 48.61/48.84           (k2_pre_topc @ sk_A @ sk_C)))),
% 48.61/48.84      inference('demod', [status(thm)], ['0', '3'])).
% 48.61/48.84  thf('5', plain,
% 48.61/48.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 48.61/48.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.61/48.84  thf(dt_k2_pre_topc, axiom,
% 48.61/48.84    (![A:$i,B:$i]:
% 48.61/48.84     ( ( ( l1_pre_topc @ A ) & 
% 48.61/48.84         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 48.61/48.84       ( m1_subset_1 @
% 48.61/48.84         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 48.61/48.84  thf('6', plain,
% 48.61/48.84      (![X20 : $i, X21 : $i]:
% 48.61/48.84         (~ (l1_pre_topc @ X20)
% 48.61/48.84          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 48.61/48.84          | (m1_subset_1 @ (k2_pre_topc @ X20 @ X21) @ 
% 48.61/48.84             (k1_zfmisc_1 @ (u1_struct_0 @ X20))))),
% 48.61/48.84      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 48.61/48.84  thf('7', plain,
% 48.61/48.84      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 48.61/48.84         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 48.61/48.84        | ~ (l1_pre_topc @ sk_A))),
% 48.61/48.84      inference('sup-', [status(thm)], ['5', '6'])).
% 48.61/48.84  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 48.61/48.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.61/48.84  thf('9', plain,
% 48.61/48.84      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 48.61/48.84        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 48.61/48.84      inference('demod', [status(thm)], ['7', '8'])).
% 48.61/48.84  thf('10', plain,
% 48.61/48.84      (![X12 : $i, X13 : $i, X14 : $i]:
% 48.61/48.84         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 48.61/48.84          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 48.61/48.84      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 48.61/48.84  thf('11', plain,
% 48.61/48.84      (![X0 : $i]:
% 48.61/48.84         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 48.61/48.84           (k2_pre_topc @ sk_A @ sk_C))
% 48.61/48.84           = (k3_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ sk_C)))),
% 48.61/48.84      inference('sup-', [status(thm)], ['9', '10'])).
% 48.61/48.84  thf('12', plain,
% 48.61/48.84      (~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 48.61/48.84          (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 48.61/48.84           (k2_pre_topc @ sk_A @ sk_C)))),
% 48.61/48.84      inference('demod', [status(thm)], ['4', '11'])).
% 48.61/48.84  thf(commutativity_k2_tarski, axiom,
% 48.61/48.84    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 48.61/48.84  thf('13', plain,
% 48.61/48.84      (![X10 : $i, X11 : $i]:
% 48.61/48.84         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 48.61/48.84      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 48.61/48.84  thf(t12_setfam_1, axiom,
% 48.61/48.84    (![A:$i,B:$i]:
% 48.61/48.84     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 48.61/48.84  thf('14', plain,
% 48.61/48.84      (![X15 : $i, X16 : $i]:
% 48.61/48.84         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 48.61/48.84      inference('cnf', [status(esa)], [t12_setfam_1])).
% 48.61/48.84  thf('15', plain,
% 48.61/48.84      (![X0 : $i, X1 : $i]:
% 48.61/48.84         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 48.61/48.84      inference('sup+', [status(thm)], ['13', '14'])).
% 48.61/48.84  thf('16', plain,
% 48.61/48.84      (![X15 : $i, X16 : $i]:
% 48.61/48.84         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 48.61/48.84      inference('cnf', [status(esa)], [t12_setfam_1])).
% 48.61/48.84  thf('17', plain,
% 48.61/48.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 48.61/48.84      inference('sup+', [status(thm)], ['15', '16'])).
% 48.61/48.84  thf('18', plain,
% 48.61/48.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 48.61/48.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.61/48.84  thf('19', plain,
% 48.61/48.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 48.61/48.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.61/48.84  thf(t3_subset, axiom,
% 48.61/48.84    (![A:$i,B:$i]:
% 48.61/48.84     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 48.61/48.84  thf('20', plain,
% 48.61/48.84      (![X17 : $i, X18 : $i]:
% 48.61/48.84         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 48.61/48.84      inference('cnf', [status(esa)], [t3_subset])).
% 48.61/48.84  thf('21', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 48.61/48.84      inference('sup-', [status(thm)], ['19', '20'])).
% 48.61/48.84  thf(t17_xboole_1, axiom,
% 48.61/48.84    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 48.61/48.84  thf('22', plain,
% 48.61/48.84      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 48.61/48.84      inference('cnf', [status(esa)], [t17_xboole_1])).
% 48.61/48.84  thf(t12_xboole_1, axiom,
% 48.61/48.84    (![A:$i,B:$i]:
% 48.61/48.84     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 48.61/48.84  thf('23', plain,
% 48.61/48.84      (![X3 : $i, X4 : $i]:
% 48.61/48.84         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 48.61/48.84      inference('cnf', [status(esa)], [t12_xboole_1])).
% 48.61/48.84  thf('24', plain,
% 48.61/48.84      (![X0 : $i, X1 : $i]:
% 48.61/48.84         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 48.61/48.84      inference('sup-', [status(thm)], ['22', '23'])).
% 48.61/48.84  thf(t11_xboole_1, axiom,
% 48.61/48.84    (![A:$i,B:$i,C:$i]:
% 48.61/48.84     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 48.61/48.84  thf('25', plain,
% 48.61/48.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.61/48.84         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 48.61/48.84      inference('cnf', [status(esa)], [t11_xboole_1])).
% 48.61/48.84  thf('26', plain,
% 48.61/48.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.61/48.84         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X0 @ X2) @ X1))),
% 48.61/48.84      inference('sup-', [status(thm)], ['24', '25'])).
% 48.61/48.84  thf('27', plain,
% 48.61/48.84      (![X0 : $i]:
% 48.61/48.84         (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ (u1_struct_0 @ sk_A))),
% 48.61/48.84      inference('sup-', [status(thm)], ['21', '26'])).
% 48.61/48.84  thf('28', plain,
% 48.61/48.84      (![X17 : $i, X19 : $i]:
% 48.61/48.84         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 48.61/48.84      inference('cnf', [status(esa)], [t3_subset])).
% 48.61/48.84  thf('29', plain,
% 48.61/48.84      (![X0 : $i]:
% 48.61/48.84         (m1_subset_1 @ (k3_xboole_0 @ sk_C @ X0) @ 
% 48.61/48.84          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 48.61/48.84      inference('sup-', [status(thm)], ['27', '28'])).
% 48.61/48.84  thf(t49_pre_topc, axiom,
% 48.61/48.84    (![A:$i]:
% 48.61/48.84     ( ( l1_pre_topc @ A ) =>
% 48.61/48.84       ( ![B:$i]:
% 48.61/48.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 48.61/48.84           ( ![C:$i]:
% 48.61/48.84             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 48.61/48.84               ( ( r1_tarski @ B @ C ) =>
% 48.61/48.84                 ( r1_tarski @
% 48.61/48.84                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 48.61/48.84  thf('30', plain,
% 48.61/48.84      (![X22 : $i, X23 : $i, X24 : $i]:
% 48.61/48.84         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 48.61/48.84          | ~ (r1_tarski @ X22 @ X24)
% 48.61/48.84          | (r1_tarski @ (k2_pre_topc @ X23 @ X22) @ (k2_pre_topc @ X23 @ X24))
% 48.61/48.84          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 48.61/48.84          | ~ (l1_pre_topc @ X23))),
% 48.61/48.84      inference('cnf', [status(esa)], [t49_pre_topc])).
% 48.61/48.84  thf('31', plain,
% 48.61/48.84      (![X0 : $i, X1 : $i]:
% 48.61/48.84         (~ (l1_pre_topc @ sk_A)
% 48.61/48.84          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 48.61/48.84          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0)) @ 
% 48.61/48.84             (k2_pre_topc @ sk_A @ X1))
% 48.61/48.84          | ~ (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ X1))),
% 48.61/48.84      inference('sup-', [status(thm)], ['29', '30'])).
% 48.61/48.84  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 48.61/48.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.61/48.84  thf('33', plain,
% 48.61/48.84      (![X0 : $i, X1 : $i]:
% 48.61/48.84         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 48.61/48.84          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0)) @ 
% 48.61/48.84             (k2_pre_topc @ sk_A @ X1))
% 48.61/48.84          | ~ (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ X1))),
% 48.61/48.84      inference('demod', [status(thm)], ['31', '32'])).
% 48.61/48.84  thf('34', plain,
% 48.61/48.84      (![X0 : $i]:
% 48.61/48.84         (~ (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ sk_C)
% 48.61/48.84          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0)) @ 
% 48.61/48.84             (k2_pre_topc @ sk_A @ sk_C)))),
% 48.61/48.84      inference('sup-', [status(thm)], ['18', '33'])).
% 48.61/48.84  thf('35', plain,
% 48.61/48.84      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 48.61/48.84      inference('cnf', [status(esa)], [t17_xboole_1])).
% 48.61/48.84  thf('36', plain,
% 48.61/48.84      (![X0 : $i]:
% 48.61/48.84         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0)) @ 
% 48.61/48.84          (k2_pre_topc @ sk_A @ sk_C))),
% 48.61/48.84      inference('demod', [status(thm)], ['34', '35'])).
% 48.61/48.84  thf('37', plain,
% 48.61/48.84      (![X0 : $i]:
% 48.61/48.84         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 48.61/48.84          (k2_pre_topc @ sk_A @ sk_C))),
% 48.61/48.84      inference('sup+', [status(thm)], ['17', '36'])).
% 48.61/48.84  thf('38', plain,
% 48.61/48.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 48.61/48.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.61/48.84  thf('39', plain,
% 48.61/48.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 48.61/48.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.61/48.84  thf('40', plain,
% 48.61/48.84      (![X17 : $i, X18 : $i]:
% 48.61/48.84         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 48.61/48.84      inference('cnf', [status(esa)], [t3_subset])).
% 48.61/48.84  thf('41', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 48.61/48.84      inference('sup-', [status(thm)], ['39', '40'])).
% 48.61/48.84  thf('42', plain,
% 48.61/48.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.61/48.84         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X0 @ X2) @ X1))),
% 48.61/48.84      inference('sup-', [status(thm)], ['24', '25'])).
% 48.61/48.84  thf('43', plain,
% 48.61/48.84      (![X0 : $i]:
% 48.61/48.84         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 48.61/48.84      inference('sup-', [status(thm)], ['41', '42'])).
% 48.61/48.84  thf('44', plain,
% 48.61/48.84      (![X17 : $i, X19 : $i]:
% 48.61/48.84         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 48.61/48.84      inference('cnf', [status(esa)], [t3_subset])).
% 48.61/48.84  thf('45', plain,
% 48.61/48.84      (![X0 : $i]:
% 48.61/48.84         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 48.61/48.84          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 48.61/48.84      inference('sup-', [status(thm)], ['43', '44'])).
% 48.61/48.84  thf('46', plain,
% 48.61/48.84      (![X22 : $i, X23 : $i, X24 : $i]:
% 48.61/48.84         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 48.61/48.84          | ~ (r1_tarski @ X22 @ X24)
% 48.61/48.84          | (r1_tarski @ (k2_pre_topc @ X23 @ X22) @ (k2_pre_topc @ X23 @ X24))
% 48.61/48.84          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 48.61/48.84          | ~ (l1_pre_topc @ X23))),
% 48.61/48.84      inference('cnf', [status(esa)], [t49_pre_topc])).
% 48.61/48.84  thf('47', plain,
% 48.61/48.84      (![X0 : $i, X1 : $i]:
% 48.61/48.84         (~ (l1_pre_topc @ sk_A)
% 48.61/48.84          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 48.61/48.84          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 48.61/48.84             (k2_pre_topc @ sk_A @ X1))
% 48.61/48.84          | ~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ X1))),
% 48.61/48.84      inference('sup-', [status(thm)], ['45', '46'])).
% 48.61/48.84  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 48.61/48.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.61/48.84  thf('49', plain,
% 48.61/48.84      (![X0 : $i, X1 : $i]:
% 48.61/48.84         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 48.61/48.84          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 48.61/48.84             (k2_pre_topc @ sk_A @ X1))
% 48.61/48.84          | ~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ X1))),
% 48.61/48.84      inference('demod', [status(thm)], ['47', '48'])).
% 48.61/48.84  thf('50', plain,
% 48.61/48.84      (![X0 : $i]:
% 48.61/48.84         (~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)
% 48.61/48.84          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 48.61/48.84             (k2_pre_topc @ sk_A @ sk_B)))),
% 48.61/48.84      inference('sup-', [status(thm)], ['38', '49'])).
% 48.61/48.84  thf('51', plain,
% 48.61/48.84      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 48.61/48.84      inference('cnf', [status(esa)], [t17_xboole_1])).
% 48.61/48.84  thf('52', plain,
% 48.61/48.84      (![X0 : $i]:
% 48.61/48.84         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 48.61/48.84          (k2_pre_topc @ sk_A @ sk_B))),
% 48.61/48.84      inference('demod', [status(thm)], ['50', '51'])).
% 48.61/48.84  thf(t19_xboole_1, axiom,
% 48.61/48.84    (![A:$i,B:$i,C:$i]:
% 48.61/48.84     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 48.61/48.84       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 48.61/48.84  thf('53', plain,
% 48.61/48.84      (![X7 : $i, X8 : $i, X9 : $i]:
% 48.61/48.84         (~ (r1_tarski @ X7 @ X8)
% 48.61/48.84          | ~ (r1_tarski @ X7 @ X9)
% 48.61/48.84          | (r1_tarski @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 48.61/48.84      inference('cnf', [status(esa)], [t19_xboole_1])).
% 48.61/48.84  thf('54', plain,
% 48.61/48.84      (![X0 : $i, X1 : $i]:
% 48.61/48.84         ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 48.61/48.84           (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X1))
% 48.61/48.84          | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 48.61/48.84               X1))),
% 48.61/48.84      inference('sup-', [status(thm)], ['52', '53'])).
% 48.61/48.84  thf('55', plain,
% 48.61/48.84      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 48.61/48.84        (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 48.61/48.84         (k2_pre_topc @ sk_A @ sk_C)))),
% 48.61/48.84      inference('sup-', [status(thm)], ['37', '54'])).
% 48.61/48.84  thf('56', plain, ($false), inference('demod', [status(thm)], ['12', '55'])).
% 48.61/48.84  
% 48.61/48.84  % SZS output end Refutation
% 48.61/48.84  
% 48.61/48.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

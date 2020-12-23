%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OFwHHw6uPW

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:18 EST 2020

% Result     : Theorem 5.44s
% Output     : Refutation 5.44s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 132 expanded)
%              Number of leaves         :   22 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  696 (1607 expanded)
%              Number of equality atoms :   17 (  44 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
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

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X7 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( r1_tarski @ ( k2_pre_topc @ X18 @ X17 ) @ ( k2_pre_topc @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_C )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['17','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X7 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( r1_tarski @ ( k2_pre_topc @ X18 @ X17 ) @ ( k2_pre_topc @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('49',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X1 ) )
      | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('53',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['12','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OFwHHw6uPW
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 5.44/5.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.44/5.62  % Solved by: fo/fo7.sh
% 5.44/5.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.44/5.62  % done 3648 iterations in 5.166s
% 5.44/5.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.44/5.62  % SZS output start Refutation
% 5.44/5.62  thf(sk_B_type, type, sk_B: $i).
% 5.44/5.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.44/5.62  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 5.44/5.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.44/5.62  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 5.44/5.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.44/5.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.44/5.62  thf(sk_C_type, type, sk_C: $i).
% 5.44/5.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.44/5.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.44/5.62  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 5.44/5.62  thf(sk_A_type, type, sk_A: $i).
% 5.44/5.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.44/5.62  thf(t51_pre_topc, conjecture,
% 5.44/5.62    (![A:$i]:
% 5.44/5.62     ( ( l1_pre_topc @ A ) =>
% 5.44/5.62       ( ![B:$i]:
% 5.44/5.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.44/5.62           ( ![C:$i]:
% 5.44/5.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.44/5.62               ( r1_tarski @
% 5.44/5.62                 ( k2_pre_topc @
% 5.44/5.62                   A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 5.44/5.62                 ( k9_subset_1 @
% 5.44/5.62                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 5.44/5.62                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 5.44/5.62  thf(zf_stmt_0, negated_conjecture,
% 5.44/5.62    (~( ![A:$i]:
% 5.44/5.62        ( ( l1_pre_topc @ A ) =>
% 5.44/5.62          ( ![B:$i]:
% 5.44/5.62            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.44/5.62              ( ![C:$i]:
% 5.44/5.62                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.44/5.62                  ( r1_tarski @
% 5.44/5.62                    ( k2_pre_topc @
% 5.44/5.62                      A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 5.44/5.62                    ( k9_subset_1 @
% 5.44/5.62                      ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 5.44/5.62                      ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) )),
% 5.44/5.62    inference('cnf.neg', [status(esa)], [t51_pre_topc])).
% 5.44/5.62  thf('0', plain,
% 5.44/5.62      (~ (r1_tarski @ 
% 5.44/5.62          (k2_pre_topc @ sk_A @ 
% 5.44/5.62           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 5.44/5.62          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 5.44/5.62           (k2_pre_topc @ sk_A @ sk_C)))),
% 5.44/5.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.62  thf('1', plain,
% 5.44/5.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.44/5.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.62  thf(redefinition_k9_subset_1, axiom,
% 5.44/5.62    (![A:$i,B:$i,C:$i]:
% 5.44/5.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.44/5.62       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 5.44/5.62  thf('2', plain,
% 5.44/5.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.44/5.62         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 5.44/5.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 5.44/5.62      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 5.44/5.62  thf('3', plain,
% 5.44/5.62      (![X0 : $i]:
% 5.44/5.62         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 5.44/5.62           = (k3_xboole_0 @ X0 @ sk_C))),
% 5.44/5.62      inference('sup-', [status(thm)], ['1', '2'])).
% 5.44/5.62  thf('4', plain,
% 5.44/5.62      (~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 5.44/5.62          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 5.44/5.62           (k2_pre_topc @ sk_A @ sk_C)))),
% 5.44/5.62      inference('demod', [status(thm)], ['0', '3'])).
% 5.44/5.62  thf('5', plain,
% 5.44/5.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.44/5.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.62  thf(dt_k2_pre_topc, axiom,
% 5.44/5.62    (![A:$i,B:$i]:
% 5.44/5.62     ( ( ( l1_pre_topc @ A ) & 
% 5.44/5.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.44/5.62       ( m1_subset_1 @
% 5.44/5.62         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 5.44/5.62  thf('6', plain,
% 5.44/5.62      (![X15 : $i, X16 : $i]:
% 5.44/5.62         (~ (l1_pre_topc @ X15)
% 5.44/5.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 5.44/5.62          | (m1_subset_1 @ (k2_pre_topc @ X15 @ X16) @ 
% 5.44/5.62             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 5.44/5.62      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 5.44/5.62  thf('7', plain,
% 5.44/5.62      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 5.44/5.62         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.44/5.62        | ~ (l1_pre_topc @ sk_A))),
% 5.44/5.62      inference('sup-', [status(thm)], ['5', '6'])).
% 5.44/5.62  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 5.44/5.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.62  thf('9', plain,
% 5.44/5.62      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 5.44/5.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.44/5.62      inference('demod', [status(thm)], ['7', '8'])).
% 5.44/5.62  thf('10', plain,
% 5.44/5.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.44/5.62         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 5.44/5.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 5.44/5.62      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 5.44/5.62  thf('11', plain,
% 5.44/5.62      (![X0 : $i]:
% 5.44/5.62         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 5.44/5.62           (k2_pre_topc @ sk_A @ sk_C))
% 5.44/5.62           = (k3_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ sk_C)))),
% 5.44/5.62      inference('sup-', [status(thm)], ['9', '10'])).
% 5.44/5.62  thf('12', plain,
% 5.44/5.62      (~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 5.44/5.62          (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 5.44/5.62           (k2_pre_topc @ sk_A @ sk_C)))),
% 5.44/5.62      inference('demod', [status(thm)], ['4', '11'])).
% 5.44/5.62  thf(commutativity_k2_tarski, axiom,
% 5.44/5.62    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 5.44/5.62  thf('13', plain,
% 5.44/5.62      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 5.44/5.62      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.44/5.62  thf(t12_setfam_1, axiom,
% 5.44/5.62    (![A:$i,B:$i]:
% 5.44/5.62     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.44/5.62  thf('14', plain,
% 5.44/5.62      (![X13 : $i, X14 : $i]:
% 5.44/5.62         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 5.44/5.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 5.44/5.62  thf('15', plain,
% 5.44/5.62      (![X0 : $i, X1 : $i]:
% 5.44/5.62         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 5.44/5.62      inference('sup+', [status(thm)], ['13', '14'])).
% 5.44/5.62  thf('16', plain,
% 5.44/5.62      (![X13 : $i, X14 : $i]:
% 5.44/5.62         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 5.44/5.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 5.44/5.62  thf('17', plain,
% 5.44/5.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.44/5.62      inference('sup+', [status(thm)], ['15', '16'])).
% 5.44/5.62  thf('18', plain,
% 5.44/5.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.44/5.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.62  thf('19', plain,
% 5.44/5.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.44/5.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.62  thf(dt_k9_subset_1, axiom,
% 5.44/5.62    (![A:$i,B:$i,C:$i]:
% 5.44/5.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.44/5.62       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 5.44/5.62  thf('20', plain,
% 5.44/5.62      (![X7 : $i, X8 : $i, X9 : $i]:
% 5.44/5.62         ((m1_subset_1 @ (k9_subset_1 @ X7 @ X8 @ X9) @ (k1_zfmisc_1 @ X7))
% 5.44/5.62          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X7)))),
% 5.44/5.62      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 5.44/5.62  thf('21', plain,
% 5.44/5.62      (![X0 : $i]:
% 5.44/5.62         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 5.44/5.62          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.44/5.62      inference('sup-', [status(thm)], ['19', '20'])).
% 5.44/5.62  thf('22', plain,
% 5.44/5.62      (![X0 : $i]:
% 5.44/5.62         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 5.44/5.62           = (k3_xboole_0 @ X0 @ sk_C))),
% 5.44/5.62      inference('sup-', [status(thm)], ['1', '2'])).
% 5.44/5.62  thf('23', plain,
% 5.44/5.62      (![X0 : $i]:
% 5.44/5.62         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 5.44/5.62          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.44/5.62      inference('demod', [status(thm)], ['21', '22'])).
% 5.44/5.62  thf(t49_pre_topc, axiom,
% 5.44/5.62    (![A:$i]:
% 5.44/5.62     ( ( l1_pre_topc @ A ) =>
% 5.44/5.62       ( ![B:$i]:
% 5.44/5.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.44/5.62           ( ![C:$i]:
% 5.44/5.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.44/5.62               ( ( r1_tarski @ B @ C ) =>
% 5.44/5.62                 ( r1_tarski @
% 5.44/5.62                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 5.44/5.62  thf('24', plain,
% 5.44/5.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 5.44/5.62         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 5.44/5.62          | ~ (r1_tarski @ X17 @ X19)
% 5.44/5.62          | (r1_tarski @ (k2_pre_topc @ X18 @ X17) @ (k2_pre_topc @ X18 @ X19))
% 5.44/5.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 5.44/5.62          | ~ (l1_pre_topc @ X18))),
% 5.44/5.62      inference('cnf', [status(esa)], [t49_pre_topc])).
% 5.44/5.62  thf('25', plain,
% 5.44/5.62      (![X0 : $i, X1 : $i]:
% 5.44/5.62         (~ (l1_pre_topc @ sk_A)
% 5.44/5.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.44/5.62          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 5.44/5.62             (k2_pre_topc @ sk_A @ X1))
% 5.44/5.62          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ X1))),
% 5.44/5.62      inference('sup-', [status(thm)], ['23', '24'])).
% 5.44/5.62  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 5.44/5.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.62  thf('27', plain,
% 5.44/5.62      (![X0 : $i, X1 : $i]:
% 5.44/5.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.44/5.62          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 5.44/5.62             (k2_pre_topc @ sk_A @ X1))
% 5.44/5.62          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ X1))),
% 5.44/5.62      inference('demod', [status(thm)], ['25', '26'])).
% 5.44/5.62  thf('28', plain,
% 5.44/5.62      (![X0 : $i]:
% 5.44/5.62         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_C)
% 5.44/5.62          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 5.44/5.62             (k2_pre_topc @ sk_A @ sk_C)))),
% 5.44/5.62      inference('sup-', [status(thm)], ['18', '27'])).
% 5.44/5.62  thf('29', plain,
% 5.44/5.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.44/5.62      inference('sup+', [status(thm)], ['15', '16'])).
% 5.44/5.62  thf(t17_xboole_1, axiom,
% 5.44/5.62    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 5.44/5.62  thf('30', plain,
% 5.44/5.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 5.44/5.62      inference('cnf', [status(esa)], [t17_xboole_1])).
% 5.44/5.62  thf('31', plain,
% 5.44/5.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 5.44/5.62      inference('sup+', [status(thm)], ['29', '30'])).
% 5.44/5.62  thf('32', plain,
% 5.44/5.62      (![X0 : $i]:
% 5.44/5.62         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 5.44/5.62          (k2_pre_topc @ sk_A @ sk_C))),
% 5.44/5.62      inference('demod', [status(thm)], ['28', '31'])).
% 5.44/5.62  thf('33', plain,
% 5.44/5.62      (![X0 : $i]:
% 5.44/5.62         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0)) @ 
% 5.44/5.62          (k2_pre_topc @ sk_A @ sk_C))),
% 5.44/5.62      inference('sup+', [status(thm)], ['17', '32'])).
% 5.44/5.62  thf('34', plain,
% 5.44/5.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.44/5.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.62  thf('35', plain,
% 5.44/5.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.44/5.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.62  thf('36', plain,
% 5.44/5.62      (![X7 : $i, X8 : $i, X9 : $i]:
% 5.44/5.62         ((m1_subset_1 @ (k9_subset_1 @ X7 @ X8 @ X9) @ (k1_zfmisc_1 @ X7))
% 5.44/5.62          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X7)))),
% 5.44/5.62      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 5.44/5.62  thf('37', plain,
% 5.44/5.62      (![X0 : $i]:
% 5.44/5.62         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 5.44/5.62          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.44/5.62      inference('sup-', [status(thm)], ['35', '36'])).
% 5.44/5.62  thf('38', plain,
% 5.44/5.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.44/5.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.62  thf('39', plain,
% 5.44/5.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.44/5.62         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 5.44/5.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 5.44/5.62      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 5.44/5.62  thf('40', plain,
% 5.44/5.62      (![X0 : $i]:
% 5.44/5.62         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 5.44/5.62           = (k3_xboole_0 @ X0 @ sk_B))),
% 5.44/5.62      inference('sup-', [status(thm)], ['38', '39'])).
% 5.44/5.62  thf('41', plain,
% 5.44/5.62      (![X0 : $i]:
% 5.44/5.62         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 5.44/5.62          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.44/5.62      inference('demod', [status(thm)], ['37', '40'])).
% 5.44/5.62  thf('42', plain,
% 5.44/5.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 5.44/5.62         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 5.44/5.62          | ~ (r1_tarski @ X17 @ X19)
% 5.44/5.62          | (r1_tarski @ (k2_pre_topc @ X18 @ X17) @ (k2_pre_topc @ X18 @ X19))
% 5.44/5.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 5.44/5.62          | ~ (l1_pre_topc @ X18))),
% 5.44/5.62      inference('cnf', [status(esa)], [t49_pre_topc])).
% 5.44/5.62  thf('43', plain,
% 5.44/5.62      (![X0 : $i, X1 : $i]:
% 5.44/5.62         (~ (l1_pre_topc @ sk_A)
% 5.44/5.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.44/5.62          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 5.44/5.62             (k2_pre_topc @ sk_A @ X1))
% 5.44/5.62          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ X1))),
% 5.44/5.62      inference('sup-', [status(thm)], ['41', '42'])).
% 5.44/5.62  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 5.44/5.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.44/5.62  thf('45', plain,
% 5.44/5.62      (![X0 : $i, X1 : $i]:
% 5.44/5.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.44/5.62          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 5.44/5.62             (k2_pre_topc @ sk_A @ X1))
% 5.44/5.62          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ X1))),
% 5.44/5.62      inference('demod', [status(thm)], ['43', '44'])).
% 5.44/5.62  thf('46', plain,
% 5.44/5.62      (![X0 : $i]:
% 5.44/5.62         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B)
% 5.44/5.62          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 5.44/5.62             (k2_pre_topc @ sk_A @ sk_B)))),
% 5.44/5.62      inference('sup-', [status(thm)], ['34', '45'])).
% 5.44/5.62  thf('47', plain,
% 5.44/5.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 5.44/5.62      inference('sup+', [status(thm)], ['29', '30'])).
% 5.44/5.62  thf('48', plain,
% 5.44/5.62      (![X0 : $i]:
% 5.44/5.62         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 5.44/5.62          (k2_pre_topc @ sk_A @ sk_B))),
% 5.44/5.62      inference('demod', [status(thm)], ['46', '47'])).
% 5.44/5.62  thf(t19_xboole_1, axiom,
% 5.44/5.62    (![A:$i,B:$i,C:$i]:
% 5.44/5.62     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 5.44/5.62       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 5.44/5.62  thf('49', plain,
% 5.44/5.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 5.44/5.62         (~ (r1_tarski @ X2 @ X3)
% 5.44/5.62          | ~ (r1_tarski @ X2 @ X4)
% 5.44/5.62          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 5.44/5.62      inference('cnf', [status(esa)], [t19_xboole_1])).
% 5.44/5.62  thf('50', plain,
% 5.44/5.62      (![X0 : $i, X1 : $i]:
% 5.44/5.62         ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 5.44/5.62           (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X1))
% 5.44/5.62          | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 5.44/5.62               X1))),
% 5.44/5.62      inference('sup-', [status(thm)], ['48', '49'])).
% 5.44/5.62  thf('51', plain,
% 5.44/5.62      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)) @ 
% 5.44/5.62        (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 5.44/5.62         (k2_pre_topc @ sk_A @ sk_C)))),
% 5.44/5.62      inference('sup-', [status(thm)], ['33', '50'])).
% 5.44/5.62  thf('52', plain,
% 5.44/5.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.44/5.62      inference('sup+', [status(thm)], ['15', '16'])).
% 5.44/5.62  thf('53', plain,
% 5.44/5.62      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 5.44/5.62        (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 5.44/5.62         (k2_pre_topc @ sk_A @ sk_C)))),
% 5.44/5.62      inference('demod', [status(thm)], ['51', '52'])).
% 5.44/5.62  thf('54', plain, ($false), inference('demod', [status(thm)], ['12', '53'])).
% 5.44/5.62  
% 5.44/5.62  % SZS output end Refutation
% 5.44/5.62  
% 5.44/5.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

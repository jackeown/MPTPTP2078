%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iUsVjPtiQq

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:19 EST 2020

% Result     : Theorem 5.49s
% Output     : Refutation 5.49s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 106 expanded)
%              Number of leaves         :   19 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  657 (1419 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
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

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X7 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('19',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( r1_tarski @ ( k2_pre_topc @ X16 @ X15 ) @ ( k2_pre_topc @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ X1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_C )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['13','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X7 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( r1_tarski @ ( k2_pre_topc @ X16 @ X15 ) @ ( k2_pre_topc @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('45',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ( r1_tarski @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X1 ) )
      | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['12','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iUsVjPtiQq
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:03:51 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 5.49/5.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.49/5.72  % Solved by: fo/fo7.sh
% 5.49/5.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.49/5.72  % done 3762 iterations in 5.278s
% 5.49/5.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.49/5.72  % SZS output start Refutation
% 5.49/5.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.49/5.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.49/5.72  thf(sk_A_type, type, sk_A: $i).
% 5.49/5.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.49/5.72  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 5.49/5.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.49/5.72  thf(sk_B_type, type, sk_B: $i).
% 5.49/5.72  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.49/5.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.49/5.72  thf(sk_C_type, type, sk_C: $i).
% 5.49/5.72  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 5.49/5.72  thf(t51_pre_topc, conjecture,
% 5.49/5.72    (![A:$i]:
% 5.49/5.72     ( ( l1_pre_topc @ A ) =>
% 5.49/5.72       ( ![B:$i]:
% 5.49/5.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.49/5.72           ( ![C:$i]:
% 5.49/5.72             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.49/5.72               ( r1_tarski @
% 5.49/5.72                 ( k2_pre_topc @
% 5.49/5.72                   A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 5.49/5.72                 ( k9_subset_1 @
% 5.49/5.72                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 5.49/5.72                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 5.49/5.72  thf(zf_stmt_0, negated_conjecture,
% 5.49/5.72    (~( ![A:$i]:
% 5.49/5.72        ( ( l1_pre_topc @ A ) =>
% 5.49/5.72          ( ![B:$i]:
% 5.49/5.72            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.49/5.72              ( ![C:$i]:
% 5.49/5.72                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.49/5.72                  ( r1_tarski @
% 5.49/5.72                    ( k2_pre_topc @
% 5.49/5.72                      A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 5.49/5.72                    ( k9_subset_1 @
% 5.49/5.72                      ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 5.49/5.72                      ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) )),
% 5.49/5.72    inference('cnf.neg', [status(esa)], [t51_pre_topc])).
% 5.49/5.72  thf('0', plain,
% 5.49/5.72      (~ (r1_tarski @ 
% 5.49/5.72          (k2_pre_topc @ sk_A @ 
% 5.49/5.72           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 5.49/5.72          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 5.49/5.72           (k2_pre_topc @ sk_A @ sk_C)))),
% 5.49/5.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.72  thf('1', plain,
% 5.49/5.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.49/5.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.72  thf(redefinition_k9_subset_1, axiom,
% 5.49/5.72    (![A:$i,B:$i,C:$i]:
% 5.49/5.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.49/5.72       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 5.49/5.72  thf('2', plain,
% 5.49/5.72      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.49/5.72         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 5.49/5.72          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 5.49/5.72      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 5.49/5.72  thf('3', plain,
% 5.49/5.72      (![X0 : $i]:
% 5.49/5.72         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 5.49/5.72           = (k3_xboole_0 @ X0 @ sk_C))),
% 5.49/5.72      inference('sup-', [status(thm)], ['1', '2'])).
% 5.49/5.72  thf('4', plain,
% 5.49/5.72      (~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 5.49/5.72          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 5.49/5.72           (k2_pre_topc @ sk_A @ sk_C)))),
% 5.49/5.72      inference('demod', [status(thm)], ['0', '3'])).
% 5.49/5.72  thf('5', plain,
% 5.49/5.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.49/5.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.72  thf(dt_k2_pre_topc, axiom,
% 5.49/5.72    (![A:$i,B:$i]:
% 5.49/5.72     ( ( ( l1_pre_topc @ A ) & 
% 5.49/5.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.49/5.72       ( m1_subset_1 @
% 5.49/5.72         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 5.49/5.72  thf('6', plain,
% 5.49/5.72      (![X13 : $i, X14 : $i]:
% 5.49/5.72         (~ (l1_pre_topc @ X13)
% 5.49/5.72          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 5.49/5.72          | (m1_subset_1 @ (k2_pre_topc @ X13 @ X14) @ 
% 5.49/5.72             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 5.49/5.72      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 5.49/5.72  thf('7', plain,
% 5.49/5.72      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 5.49/5.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.49/5.72        | ~ (l1_pre_topc @ sk_A))),
% 5.49/5.72      inference('sup-', [status(thm)], ['5', '6'])).
% 5.49/5.72  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 5.49/5.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.72  thf('9', plain,
% 5.49/5.72      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 5.49/5.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.49/5.72      inference('demod', [status(thm)], ['7', '8'])).
% 5.49/5.72  thf('10', plain,
% 5.49/5.72      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.49/5.72         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 5.49/5.72          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 5.49/5.72      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 5.49/5.72  thf('11', plain,
% 5.49/5.72      (![X0 : $i]:
% 5.49/5.72         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 5.49/5.72           (k2_pre_topc @ sk_A @ sk_C))
% 5.49/5.72           = (k3_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ sk_C)))),
% 5.49/5.72      inference('sup-', [status(thm)], ['9', '10'])).
% 5.49/5.72  thf('12', plain,
% 5.49/5.72      (~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 5.49/5.72          (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 5.49/5.72           (k2_pre_topc @ sk_A @ sk_C)))),
% 5.49/5.72      inference('demod', [status(thm)], ['4', '11'])).
% 5.49/5.72  thf(commutativity_k3_xboole_0, axiom,
% 5.49/5.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 5.49/5.72  thf('13', plain,
% 5.49/5.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.49/5.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.49/5.72  thf('14', plain,
% 5.49/5.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.49/5.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.72  thf('15', plain,
% 5.49/5.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.49/5.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.72  thf(dt_k9_subset_1, axiom,
% 5.49/5.72    (![A:$i,B:$i,C:$i]:
% 5.49/5.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.49/5.72       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 5.49/5.72  thf('16', plain,
% 5.49/5.72      (![X7 : $i, X8 : $i, X9 : $i]:
% 5.49/5.72         ((m1_subset_1 @ (k9_subset_1 @ X7 @ X8 @ X9) @ (k1_zfmisc_1 @ X7))
% 5.49/5.72          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X7)))),
% 5.49/5.72      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 5.49/5.72  thf('17', plain,
% 5.49/5.72      (![X0 : $i]:
% 5.49/5.72         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 5.49/5.72          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.49/5.72      inference('sup-', [status(thm)], ['15', '16'])).
% 5.49/5.72  thf('18', plain,
% 5.49/5.72      (![X0 : $i]:
% 5.49/5.72         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 5.49/5.72           = (k3_xboole_0 @ X0 @ sk_C))),
% 5.49/5.72      inference('sup-', [status(thm)], ['1', '2'])).
% 5.49/5.72  thf('19', plain,
% 5.49/5.72      (![X0 : $i]:
% 5.49/5.72         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 5.49/5.72          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.49/5.72      inference('demod', [status(thm)], ['17', '18'])).
% 5.49/5.72  thf(t49_pre_topc, axiom,
% 5.49/5.72    (![A:$i]:
% 5.49/5.72     ( ( l1_pre_topc @ A ) =>
% 5.49/5.72       ( ![B:$i]:
% 5.49/5.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.49/5.72           ( ![C:$i]:
% 5.49/5.72             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.49/5.72               ( ( r1_tarski @ B @ C ) =>
% 5.49/5.72                 ( r1_tarski @
% 5.49/5.72                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 5.49/5.72  thf('20', plain,
% 5.49/5.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.49/5.72         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 5.49/5.72          | ~ (r1_tarski @ X15 @ X17)
% 5.49/5.72          | (r1_tarski @ (k2_pre_topc @ X16 @ X15) @ (k2_pre_topc @ X16 @ X17))
% 5.49/5.72          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 5.49/5.72          | ~ (l1_pre_topc @ X16))),
% 5.49/5.72      inference('cnf', [status(esa)], [t49_pre_topc])).
% 5.49/5.72  thf('21', plain,
% 5.49/5.72      (![X0 : $i, X1 : $i]:
% 5.49/5.72         (~ (l1_pre_topc @ sk_A)
% 5.49/5.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.49/5.72          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 5.49/5.72             (k2_pre_topc @ sk_A @ X1))
% 5.49/5.72          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ X1))),
% 5.49/5.72      inference('sup-', [status(thm)], ['19', '20'])).
% 5.49/5.72  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 5.49/5.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.72  thf('23', plain,
% 5.49/5.72      (![X0 : $i, X1 : $i]:
% 5.49/5.72         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.49/5.72          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 5.49/5.72             (k2_pre_topc @ sk_A @ X1))
% 5.49/5.72          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ X1))),
% 5.49/5.72      inference('demod', [status(thm)], ['21', '22'])).
% 5.49/5.72  thf('24', plain,
% 5.49/5.72      (![X0 : $i]:
% 5.49/5.72         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_C)
% 5.49/5.72          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 5.49/5.72             (k2_pre_topc @ sk_A @ sk_C)))),
% 5.49/5.72      inference('sup-', [status(thm)], ['14', '23'])).
% 5.49/5.72  thf('25', plain,
% 5.49/5.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.49/5.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.49/5.72  thf(t17_xboole_1, axiom,
% 5.49/5.72    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 5.49/5.72  thf('26', plain,
% 5.49/5.72      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 5.49/5.72      inference('cnf', [status(esa)], [t17_xboole_1])).
% 5.49/5.72  thf('27', plain,
% 5.49/5.72      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 5.49/5.72      inference('sup+', [status(thm)], ['25', '26'])).
% 5.49/5.72  thf('28', plain,
% 5.49/5.72      (![X0 : $i]:
% 5.49/5.72         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C)) @ 
% 5.49/5.72          (k2_pre_topc @ sk_A @ sk_C))),
% 5.49/5.72      inference('demod', [status(thm)], ['24', '27'])).
% 5.49/5.72  thf('29', plain,
% 5.49/5.72      (![X0 : $i]:
% 5.49/5.72         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0)) @ 
% 5.49/5.72          (k2_pre_topc @ sk_A @ sk_C))),
% 5.49/5.72      inference('sup+', [status(thm)], ['13', '28'])).
% 5.49/5.72  thf('30', plain,
% 5.49/5.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.49/5.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.72  thf('31', plain,
% 5.49/5.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.49/5.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.72  thf('32', plain,
% 5.49/5.72      (![X7 : $i, X8 : $i, X9 : $i]:
% 5.49/5.72         ((m1_subset_1 @ (k9_subset_1 @ X7 @ X8 @ X9) @ (k1_zfmisc_1 @ X7))
% 5.49/5.72          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X7)))),
% 5.49/5.72      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 5.49/5.72  thf('33', plain,
% 5.49/5.72      (![X0 : $i]:
% 5.49/5.72         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 5.49/5.72          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.49/5.72      inference('sup-', [status(thm)], ['31', '32'])).
% 5.49/5.72  thf('34', plain,
% 5.49/5.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.49/5.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.72  thf('35', plain,
% 5.49/5.72      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.49/5.72         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 5.49/5.72          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 5.49/5.72      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 5.49/5.72  thf('36', plain,
% 5.49/5.72      (![X0 : $i]:
% 5.49/5.72         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 5.49/5.72           = (k3_xboole_0 @ X0 @ sk_B))),
% 5.49/5.72      inference('sup-', [status(thm)], ['34', '35'])).
% 5.49/5.72  thf('37', plain,
% 5.49/5.72      (![X0 : $i]:
% 5.49/5.72         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 5.49/5.72          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.49/5.72      inference('demod', [status(thm)], ['33', '36'])).
% 5.49/5.72  thf('38', plain,
% 5.49/5.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.49/5.72         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 5.49/5.72          | ~ (r1_tarski @ X15 @ X17)
% 5.49/5.72          | (r1_tarski @ (k2_pre_topc @ X16 @ X15) @ (k2_pre_topc @ X16 @ X17))
% 5.49/5.72          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 5.49/5.72          | ~ (l1_pre_topc @ X16))),
% 5.49/5.72      inference('cnf', [status(esa)], [t49_pre_topc])).
% 5.49/5.72  thf('39', plain,
% 5.49/5.72      (![X0 : $i, X1 : $i]:
% 5.49/5.72         (~ (l1_pre_topc @ sk_A)
% 5.49/5.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.49/5.72          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 5.49/5.72             (k2_pre_topc @ sk_A @ X1))
% 5.49/5.72          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ X1))),
% 5.49/5.72      inference('sup-', [status(thm)], ['37', '38'])).
% 5.49/5.72  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 5.49/5.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.72  thf('41', plain,
% 5.49/5.72      (![X0 : $i, X1 : $i]:
% 5.49/5.72         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.49/5.72          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 5.49/5.72             (k2_pre_topc @ sk_A @ X1))
% 5.49/5.72          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ X1))),
% 5.49/5.72      inference('demod', [status(thm)], ['39', '40'])).
% 5.49/5.72  thf('42', plain,
% 5.49/5.72      (![X0 : $i]:
% 5.49/5.72         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B)
% 5.49/5.72          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 5.49/5.72             (k2_pre_topc @ sk_A @ sk_B)))),
% 5.49/5.72      inference('sup-', [status(thm)], ['30', '41'])).
% 5.49/5.72  thf('43', plain,
% 5.49/5.72      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 5.49/5.72      inference('sup+', [status(thm)], ['25', '26'])).
% 5.49/5.72  thf('44', plain,
% 5.49/5.72      (![X0 : $i]:
% 5.49/5.72         (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 5.49/5.72          (k2_pre_topc @ sk_A @ sk_B))),
% 5.49/5.72      inference('demod', [status(thm)], ['42', '43'])).
% 5.49/5.72  thf(t19_xboole_1, axiom,
% 5.49/5.72    (![A:$i,B:$i,C:$i]:
% 5.49/5.72     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 5.49/5.72       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 5.49/5.72  thf('45', plain,
% 5.49/5.72      (![X4 : $i, X5 : $i, X6 : $i]:
% 5.49/5.72         (~ (r1_tarski @ X4 @ X5)
% 5.49/5.72          | ~ (r1_tarski @ X4 @ X6)
% 5.49/5.72          | (r1_tarski @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 5.49/5.72      inference('cnf', [status(esa)], [t19_xboole_1])).
% 5.49/5.72  thf('46', plain,
% 5.49/5.72      (![X0 : $i, X1 : $i]:
% 5.49/5.72         ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 5.49/5.72           (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X1))
% 5.49/5.72          | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 5.49/5.72               X1))),
% 5.49/5.72      inference('sup-', [status(thm)], ['44', '45'])).
% 5.49/5.72  thf('47', plain,
% 5.49/5.72      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)) @ 
% 5.49/5.72        (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 5.49/5.72         (k2_pre_topc @ sk_A @ sk_C)))),
% 5.49/5.72      inference('sup-', [status(thm)], ['29', '46'])).
% 5.49/5.72  thf('48', plain,
% 5.49/5.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.49/5.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.49/5.72  thf('49', plain,
% 5.49/5.72      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 5.49/5.72        (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 5.49/5.72         (k2_pre_topc @ sk_A @ sk_C)))),
% 5.49/5.72      inference('demod', [status(thm)], ['47', '48'])).
% 5.49/5.72  thf('50', plain, ($false), inference('demod', [status(thm)], ['12', '49'])).
% 5.49/5.72  
% 5.49/5.72  % SZS output end Refutation
% 5.49/5.72  
% 5.49/5.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

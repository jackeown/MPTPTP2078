%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LRma81Ic0Y

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:04 EST 2020

% Result     : Theorem 3.86s
% Output     : Refutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 113 expanded)
%              Number of leaves         :   26 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  651 (1522 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t50_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k1_tops_1 @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( r1_tarski @ ( k1_tops_1 @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k7_subset_1 @ X22 @ X21 @ X23 )
        = ( k4_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k7_subset_1 @ X22 @ X21 @ X23 )
        = ( k4_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X19 @ X18 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( r1_tarski @ X28 @ X30 )
      | ( r1_tarski @ ( k1_tops_1 @ X29 @ X28 ) @ ( k1_tops_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('27',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X27 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('32',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('38',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X27 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('42',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X8 )
      | ( r1_xboole_0 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ X1 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('45',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X15 @ X17 )
      | ( r1_tarski @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['12','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LRma81Ic0Y
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.86/4.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.86/4.03  % Solved by: fo/fo7.sh
% 3.86/4.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.86/4.03  % done 3611 iterations in 3.533s
% 3.86/4.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.86/4.03  % SZS output start Refutation
% 3.86/4.03  thf(sk_A_type, type, sk_A: $i).
% 3.86/4.03  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.86/4.03  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 3.86/4.03  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.86/4.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.86/4.03  thf(sk_C_type, type, sk_C: $i).
% 3.86/4.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.86/4.03  thf(sk_B_type, type, sk_B: $i).
% 3.86/4.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.86/4.03  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.86/4.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.86/4.03  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 3.86/4.03  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.86/4.03  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.86/4.03  thf(t50_tops_1, conjecture,
% 3.86/4.03    (![A:$i]:
% 3.86/4.03     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.86/4.03       ( ![B:$i]:
% 3.86/4.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.86/4.03           ( ![C:$i]:
% 3.86/4.03             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.86/4.03               ( r1_tarski @
% 3.86/4.03                 ( k1_tops_1 @
% 3.86/4.03                   A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 3.86/4.03                 ( k7_subset_1 @
% 3.86/4.03                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 3.86/4.03                   ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 3.86/4.03  thf(zf_stmt_0, negated_conjecture,
% 3.86/4.03    (~( ![A:$i]:
% 3.86/4.03        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.86/4.03          ( ![B:$i]:
% 3.86/4.03            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.86/4.03              ( ![C:$i]:
% 3.86/4.03                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.86/4.03                  ( r1_tarski @
% 3.86/4.03                    ( k1_tops_1 @
% 3.86/4.03                      A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 3.86/4.03                    ( k7_subset_1 @
% 3.86/4.03                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 3.86/4.03                      ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 3.86/4.03    inference('cnf.neg', [status(esa)], [t50_tops_1])).
% 3.86/4.03  thf('0', plain,
% 3.86/4.03      (~ (r1_tarski @ 
% 3.86/4.03          (k1_tops_1 @ sk_A @ 
% 3.86/4.03           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 3.86/4.03          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.86/4.03           (k1_tops_1 @ sk_A @ sk_C)))),
% 3.86/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.03  thf('1', plain,
% 3.86/4.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.86/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.03  thf(redefinition_k7_subset_1, axiom,
% 3.86/4.03    (![A:$i,B:$i,C:$i]:
% 3.86/4.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.86/4.03       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 3.86/4.03  thf('2', plain,
% 3.86/4.03      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.86/4.03         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 3.86/4.03          | ((k7_subset_1 @ X22 @ X21 @ X23) = (k4_xboole_0 @ X21 @ X23)))),
% 3.86/4.03      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 3.86/4.03  thf('3', plain,
% 3.86/4.03      (![X0 : $i]:
% 3.86/4.03         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.86/4.03           = (k4_xboole_0 @ sk_B @ X0))),
% 3.86/4.03      inference('sup-', [status(thm)], ['1', '2'])).
% 3.86/4.03  thf('4', plain,
% 3.86/4.03      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 3.86/4.03          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.86/4.03           (k1_tops_1 @ sk_A @ sk_C)))),
% 3.86/4.03      inference('demod', [status(thm)], ['0', '3'])).
% 3.86/4.03  thf('5', plain,
% 3.86/4.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.86/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.03  thf(dt_k1_tops_1, axiom,
% 3.86/4.03    (![A:$i,B:$i]:
% 3.86/4.03     ( ( ( l1_pre_topc @ A ) & 
% 3.86/4.03         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.86/4.03       ( m1_subset_1 @
% 3.86/4.03         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.86/4.03  thf('6', plain,
% 3.86/4.03      (![X24 : $i, X25 : $i]:
% 3.86/4.03         (~ (l1_pre_topc @ X24)
% 3.86/4.03          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 3.86/4.03          | (m1_subset_1 @ (k1_tops_1 @ X24 @ X25) @ 
% 3.86/4.03             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 3.86/4.03      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 3.86/4.03  thf('7', plain,
% 3.86/4.03      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.86/4.03         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.86/4.03        | ~ (l1_pre_topc @ sk_A))),
% 3.86/4.03      inference('sup-', [status(thm)], ['5', '6'])).
% 3.86/4.03  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 3.86/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.03  thf('9', plain,
% 3.86/4.03      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.86/4.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.86/4.03      inference('demod', [status(thm)], ['7', '8'])).
% 3.86/4.03  thf('10', plain,
% 3.86/4.03      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.86/4.03         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 3.86/4.03          | ((k7_subset_1 @ X22 @ X21 @ X23) = (k4_xboole_0 @ X21 @ X23)))),
% 3.86/4.03      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 3.86/4.03  thf('11', plain,
% 3.86/4.03      (![X0 : $i]:
% 3.86/4.03         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 3.86/4.03           = (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 3.86/4.03      inference('sup-', [status(thm)], ['9', '10'])).
% 3.86/4.03  thf('12', plain,
% 3.86/4.03      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 3.86/4.03          (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 3.86/4.03      inference('demod', [status(thm)], ['4', '11'])).
% 3.86/4.03  thf('13', plain,
% 3.86/4.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.86/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.03  thf('14', plain,
% 3.86/4.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.86/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.03  thf(dt_k7_subset_1, axiom,
% 3.86/4.03    (![A:$i,B:$i,C:$i]:
% 3.86/4.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.86/4.03       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.86/4.03  thf('15', plain,
% 3.86/4.03      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.86/4.03         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 3.86/4.03          | (m1_subset_1 @ (k7_subset_1 @ X19 @ X18 @ X20) @ 
% 3.86/4.03             (k1_zfmisc_1 @ X19)))),
% 3.86/4.03      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 3.86/4.03  thf('16', plain,
% 3.86/4.03      (![X0 : $i]:
% 3.86/4.03         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 3.86/4.03          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.86/4.03      inference('sup-', [status(thm)], ['14', '15'])).
% 3.86/4.03  thf('17', plain,
% 3.86/4.03      (![X0 : $i]:
% 3.86/4.03         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.86/4.03           = (k4_xboole_0 @ sk_B @ X0))),
% 3.86/4.03      inference('sup-', [status(thm)], ['1', '2'])).
% 3.86/4.03  thf('18', plain,
% 3.86/4.03      (![X0 : $i]:
% 3.86/4.03         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 3.86/4.03          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.86/4.03      inference('demod', [status(thm)], ['16', '17'])).
% 3.86/4.03  thf(t48_tops_1, axiom,
% 3.86/4.03    (![A:$i]:
% 3.86/4.03     ( ( l1_pre_topc @ A ) =>
% 3.86/4.03       ( ![B:$i]:
% 3.86/4.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.86/4.03           ( ![C:$i]:
% 3.86/4.03             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.86/4.03               ( ( r1_tarski @ B @ C ) =>
% 3.86/4.03                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 3.86/4.03  thf('19', plain,
% 3.86/4.03      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.86/4.03         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 3.86/4.03          | ~ (r1_tarski @ X28 @ X30)
% 3.86/4.03          | (r1_tarski @ (k1_tops_1 @ X29 @ X28) @ (k1_tops_1 @ X29 @ X30))
% 3.86/4.03          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 3.86/4.03          | ~ (l1_pre_topc @ X29))),
% 3.86/4.03      inference('cnf', [status(esa)], [t48_tops_1])).
% 3.86/4.03  thf('20', plain,
% 3.86/4.03      (![X0 : $i, X1 : $i]:
% 3.86/4.03         (~ (l1_pre_topc @ sk_A)
% 3.86/4.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.86/4.03          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 3.86/4.03             (k1_tops_1 @ sk_A @ X1))
% 3.86/4.03          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 3.86/4.03      inference('sup-', [status(thm)], ['18', '19'])).
% 3.86/4.03  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 3.86/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.03  thf('22', plain,
% 3.86/4.03      (![X0 : $i, X1 : $i]:
% 3.86/4.03         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.86/4.03          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 3.86/4.03             (k1_tops_1 @ sk_A @ X1))
% 3.86/4.03          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 3.86/4.03      inference('demod', [status(thm)], ['20', '21'])).
% 3.86/4.03  thf('23', plain,
% 3.86/4.03      (![X0 : $i]:
% 3.86/4.03         (~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 3.86/4.03          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 3.86/4.03             (k1_tops_1 @ sk_A @ sk_B)))),
% 3.86/4.03      inference('sup-', [status(thm)], ['13', '22'])).
% 3.86/4.03  thf(t36_xboole_1, axiom,
% 3.86/4.03    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 3.86/4.03  thf('24', plain,
% 3.86/4.03      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 3.86/4.03      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.86/4.03  thf('25', plain,
% 3.86/4.03      (![X0 : $i]:
% 3.86/4.03         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 3.86/4.03          (k1_tops_1 @ sk_A @ sk_B))),
% 3.86/4.03      inference('demod', [status(thm)], ['23', '24'])).
% 3.86/4.03  thf('26', plain,
% 3.86/4.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.86/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.03  thf(t44_tops_1, axiom,
% 3.86/4.03    (![A:$i]:
% 3.86/4.03     ( ( l1_pre_topc @ A ) =>
% 3.86/4.03       ( ![B:$i]:
% 3.86/4.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.86/4.03           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 3.86/4.03  thf('27', plain,
% 3.86/4.03      (![X26 : $i, X27 : $i]:
% 3.86/4.03         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 3.86/4.03          | (r1_tarski @ (k1_tops_1 @ X27 @ X26) @ X26)
% 3.86/4.03          | ~ (l1_pre_topc @ X27))),
% 3.86/4.03      inference('cnf', [status(esa)], [t44_tops_1])).
% 3.86/4.03  thf('28', plain,
% 3.86/4.03      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 3.86/4.03      inference('sup-', [status(thm)], ['26', '27'])).
% 3.86/4.03  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 3.86/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.03  thf('30', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 3.86/4.03      inference('demod', [status(thm)], ['28', '29'])).
% 3.86/4.03  thf(t12_xboole_1, axiom,
% 3.86/4.03    (![A:$i,B:$i]:
% 3.86/4.03     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 3.86/4.03  thf('31', plain,
% 3.86/4.03      (![X2 : $i, X3 : $i]:
% 3.86/4.03         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 3.86/4.03      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.86/4.03  thf('32', plain,
% 3.86/4.03      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C) = (sk_C))),
% 3.86/4.03      inference('sup-', [status(thm)], ['30', '31'])).
% 3.86/4.03  thf(t79_xboole_1, axiom,
% 3.86/4.03    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 3.86/4.03  thf('33', plain,
% 3.86/4.03      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 3.86/4.03      inference('cnf', [status(esa)], [t79_xboole_1])).
% 3.86/4.03  thf(t70_xboole_1, axiom,
% 3.86/4.03    (![A:$i,B:$i,C:$i]:
% 3.86/4.03     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 3.86/4.03            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 3.86/4.03       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 3.86/4.03            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 3.86/4.03  thf('34', plain,
% 3.86/4.03      (![X9 : $i, X10 : $i, X12 : $i]:
% 3.86/4.03         ((r1_xboole_0 @ X9 @ X10)
% 3.86/4.03          | ~ (r1_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X12)))),
% 3.86/4.03      inference('cnf', [status(esa)], [t70_xboole_1])).
% 3.86/4.03  thf('35', plain,
% 3.86/4.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.86/4.03         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)),
% 3.86/4.03      inference('sup-', [status(thm)], ['33', '34'])).
% 3.86/4.03  thf('36', plain,
% 3.86/4.03      (![X0 : $i]:
% 3.86/4.03         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ (k1_tops_1 @ sk_A @ sk_C))),
% 3.86/4.03      inference('sup+', [status(thm)], ['32', '35'])).
% 3.86/4.03  thf('37', plain,
% 3.86/4.03      (![X0 : $i]:
% 3.86/4.03         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 3.86/4.03          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.86/4.03      inference('demod', [status(thm)], ['16', '17'])).
% 3.86/4.03  thf('38', plain,
% 3.86/4.03      (![X26 : $i, X27 : $i]:
% 3.86/4.03         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 3.86/4.03          | (r1_tarski @ (k1_tops_1 @ X27 @ X26) @ X26)
% 3.86/4.03          | ~ (l1_pre_topc @ X27))),
% 3.86/4.03      inference('cnf', [status(esa)], [t44_tops_1])).
% 3.86/4.03  thf('39', plain,
% 3.86/4.03      (![X0 : $i]:
% 3.86/4.03         (~ (l1_pre_topc @ sk_A)
% 3.86/4.03          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 3.86/4.03             (k4_xboole_0 @ sk_B @ X0)))),
% 3.86/4.03      inference('sup-', [status(thm)], ['37', '38'])).
% 3.86/4.03  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 3.86/4.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.86/4.03  thf('41', plain,
% 3.86/4.03      (![X0 : $i]:
% 3.86/4.03         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 3.86/4.03          (k4_xboole_0 @ sk_B @ X0))),
% 3.86/4.03      inference('demod', [status(thm)], ['39', '40'])).
% 3.86/4.03  thf(t63_xboole_1, axiom,
% 3.86/4.03    (![A:$i,B:$i,C:$i]:
% 3.86/4.03     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 3.86/4.03       ( r1_xboole_0 @ A @ C ) ))).
% 3.86/4.03  thf('42', plain,
% 3.86/4.03      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.86/4.03         (~ (r1_tarski @ X6 @ X7)
% 3.86/4.03          | ~ (r1_xboole_0 @ X7 @ X8)
% 3.86/4.03          | (r1_xboole_0 @ X6 @ X8))),
% 3.86/4.03      inference('cnf', [status(esa)], [t63_xboole_1])).
% 3.86/4.03  thf('43', plain,
% 3.86/4.03      (![X0 : $i, X1 : $i]:
% 3.86/4.03         ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ X1)
% 3.86/4.03          | ~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 3.86/4.03      inference('sup-', [status(thm)], ['41', '42'])).
% 3.86/4.03  thf('44', plain,
% 3.86/4.03      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 3.86/4.03        (k1_tops_1 @ sk_A @ sk_C))),
% 3.86/4.03      inference('sup-', [status(thm)], ['36', '43'])).
% 3.86/4.03  thf(t86_xboole_1, axiom,
% 3.86/4.03    (![A:$i,B:$i,C:$i]:
% 3.86/4.03     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 3.86/4.03       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 3.86/4.03  thf('45', plain,
% 3.86/4.03      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.86/4.03         (~ (r1_tarski @ X15 @ X16)
% 3.86/4.03          | ~ (r1_xboole_0 @ X15 @ X17)
% 3.86/4.03          | (r1_tarski @ X15 @ (k4_xboole_0 @ X16 @ X17)))),
% 3.86/4.03      inference('cnf', [status(esa)], [t86_xboole_1])).
% 3.86/4.03  thf('46', plain,
% 3.86/4.03      (![X0 : $i]:
% 3.86/4.03         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 3.86/4.03           (k4_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))
% 3.86/4.03          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 3.86/4.03               X0))),
% 3.86/4.03      inference('sup-', [status(thm)], ['44', '45'])).
% 3.86/4.03  thf('47', plain,
% 3.86/4.03      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 3.86/4.03        (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 3.86/4.03      inference('sup-', [status(thm)], ['25', '46'])).
% 3.86/4.03  thf('48', plain, ($false), inference('demod', [status(thm)], ['12', '47'])).
% 3.86/4.03  
% 3.86/4.03  % SZS output end Refutation
% 3.86/4.03  
% 3.86/4.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

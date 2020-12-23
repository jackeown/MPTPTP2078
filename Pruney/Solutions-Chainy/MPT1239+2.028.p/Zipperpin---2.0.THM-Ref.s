%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oE0KeKI6mR

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:04 EST 2020

% Result     : Theorem 8.84s
% Output     : Refutation 8.84s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 137 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  761 (1898 expanded)
%              Number of equality atoms :   14 (  24 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X16 @ X15 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( r1_tarski @ X25 @ X27 )
      | ( r1_tarski @ ( k1_tops_1 @ X26 @ X25 ) @ ( k1_tops_1 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X24 @ X23 ) @ X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('34',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X16 @ X15 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X24 @ X23 ) @ X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) ) @ ( k4_xboole_0 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['46','49','50'])).

thf('52',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['39','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('56',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('57',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X12 @ X14 )
      | ( r1_tarski @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['12','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oE0KeKI6mR
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:41:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 8.84/9.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.84/9.05  % Solved by: fo/fo7.sh
% 8.84/9.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.84/9.05  % done 13705 iterations in 8.606s
% 8.84/9.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.84/9.05  % SZS output start Refutation
% 8.84/9.05  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 8.84/9.05  thf(sk_B_type, type, sk_B: $i).
% 8.84/9.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.84/9.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.84/9.05  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.84/9.05  thf(sk_A_type, type, sk_A: $i).
% 8.84/9.05  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 8.84/9.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.84/9.05  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 8.84/9.05  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 8.84/9.05  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.84/9.05  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 8.84/9.05  thf(sk_C_type, type, sk_C: $i).
% 8.84/9.05  thf(t50_tops_1, conjecture,
% 8.84/9.05    (![A:$i]:
% 8.84/9.05     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.84/9.05       ( ![B:$i]:
% 8.84/9.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.84/9.05           ( ![C:$i]:
% 8.84/9.05             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.84/9.05               ( r1_tarski @
% 8.84/9.05                 ( k1_tops_1 @
% 8.84/9.05                   A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 8.84/9.05                 ( k7_subset_1 @
% 8.84/9.05                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 8.84/9.05                   ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 8.84/9.05  thf(zf_stmt_0, negated_conjecture,
% 8.84/9.05    (~( ![A:$i]:
% 8.84/9.05        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.84/9.05          ( ![B:$i]:
% 8.84/9.05            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.84/9.05              ( ![C:$i]:
% 8.84/9.05                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.84/9.05                  ( r1_tarski @
% 8.84/9.05                    ( k1_tops_1 @
% 8.84/9.05                      A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 8.84/9.05                    ( k7_subset_1 @
% 8.84/9.05                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 8.84/9.05                      ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 8.84/9.05    inference('cnf.neg', [status(esa)], [t50_tops_1])).
% 8.84/9.05  thf('0', plain,
% 8.84/9.05      (~ (r1_tarski @ 
% 8.84/9.05          (k1_tops_1 @ sk_A @ 
% 8.84/9.05           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 8.84/9.05          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 8.84/9.05           (k1_tops_1 @ sk_A @ sk_C)))),
% 8.84/9.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.84/9.05  thf('1', plain,
% 8.84/9.05      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.84/9.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.84/9.05  thf(redefinition_k7_subset_1, axiom,
% 8.84/9.05    (![A:$i,B:$i,C:$i]:
% 8.84/9.05     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.84/9.05       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 8.84/9.05  thf('2', plain,
% 8.84/9.05      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.84/9.05         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 8.84/9.05          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 8.84/9.05      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.84/9.05  thf('3', plain,
% 8.84/9.05      (![X0 : $i]:
% 8.84/9.05         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.84/9.05           = (k4_xboole_0 @ sk_B @ X0))),
% 8.84/9.05      inference('sup-', [status(thm)], ['1', '2'])).
% 8.84/9.05  thf('4', plain,
% 8.84/9.05      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 8.84/9.05          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 8.84/9.05           (k1_tops_1 @ sk_A @ sk_C)))),
% 8.84/9.05      inference('demod', [status(thm)], ['0', '3'])).
% 8.84/9.05  thf('5', plain,
% 8.84/9.05      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.84/9.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.84/9.05  thf(dt_k1_tops_1, axiom,
% 8.84/9.05    (![A:$i,B:$i]:
% 8.84/9.05     ( ( ( l1_pre_topc @ A ) & 
% 8.84/9.05         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.84/9.05       ( m1_subset_1 @
% 8.84/9.05         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 8.84/9.05  thf('6', plain,
% 8.84/9.05      (![X21 : $i, X22 : $i]:
% 8.84/9.05         (~ (l1_pre_topc @ X21)
% 8.84/9.05          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 8.84/9.05          | (m1_subset_1 @ (k1_tops_1 @ X21 @ X22) @ 
% 8.84/9.05             (k1_zfmisc_1 @ (u1_struct_0 @ X21))))),
% 8.84/9.05      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 8.84/9.05  thf('7', plain,
% 8.84/9.05      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 8.84/9.05         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.84/9.05        | ~ (l1_pre_topc @ sk_A))),
% 8.84/9.05      inference('sup-', [status(thm)], ['5', '6'])).
% 8.84/9.05  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 8.84/9.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.84/9.05  thf('9', plain,
% 8.84/9.05      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 8.84/9.05        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.84/9.05      inference('demod', [status(thm)], ['7', '8'])).
% 8.84/9.05  thf('10', plain,
% 8.84/9.05      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.84/9.05         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 8.84/9.05          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 8.84/9.05      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.84/9.05  thf('11', plain,
% 8.84/9.05      (![X0 : $i]:
% 8.84/9.05         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 8.84/9.05           = (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 8.84/9.05      inference('sup-', [status(thm)], ['9', '10'])).
% 8.84/9.05  thf('12', plain,
% 8.84/9.05      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 8.84/9.05          (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 8.84/9.05      inference('demod', [status(thm)], ['4', '11'])).
% 8.84/9.05  thf('13', plain,
% 8.84/9.05      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.84/9.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.84/9.05  thf('14', plain,
% 8.84/9.05      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.84/9.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.84/9.05  thf(dt_k7_subset_1, axiom,
% 8.84/9.05    (![A:$i,B:$i,C:$i]:
% 8.84/9.05     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.84/9.05       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 8.84/9.05  thf('15', plain,
% 8.84/9.05      (![X15 : $i, X16 : $i, X17 : $i]:
% 8.84/9.05         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 8.84/9.05          | (m1_subset_1 @ (k7_subset_1 @ X16 @ X15 @ X17) @ 
% 8.84/9.05             (k1_zfmisc_1 @ X16)))),
% 8.84/9.05      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 8.84/9.05  thf('16', plain,
% 8.84/9.05      (![X0 : $i]:
% 8.84/9.05         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 8.84/9.05          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.84/9.05      inference('sup-', [status(thm)], ['14', '15'])).
% 8.84/9.06  thf('17', plain,
% 8.84/9.06      (![X0 : $i]:
% 8.84/9.06         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.84/9.06           = (k4_xboole_0 @ sk_B @ X0))),
% 8.84/9.06      inference('sup-', [status(thm)], ['1', '2'])).
% 8.84/9.06  thf('18', plain,
% 8.84/9.06      (![X0 : $i]:
% 8.84/9.06         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 8.84/9.06          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.84/9.06      inference('demod', [status(thm)], ['16', '17'])).
% 8.84/9.06  thf(t48_tops_1, axiom,
% 8.84/9.06    (![A:$i]:
% 8.84/9.06     ( ( l1_pre_topc @ A ) =>
% 8.84/9.06       ( ![B:$i]:
% 8.84/9.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.84/9.06           ( ![C:$i]:
% 8.84/9.06             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.84/9.06               ( ( r1_tarski @ B @ C ) =>
% 8.84/9.06                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 8.84/9.06  thf('19', plain,
% 8.84/9.06      (![X25 : $i, X26 : $i, X27 : $i]:
% 8.84/9.06         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 8.84/9.06          | ~ (r1_tarski @ X25 @ X27)
% 8.84/9.06          | (r1_tarski @ (k1_tops_1 @ X26 @ X25) @ (k1_tops_1 @ X26 @ X27))
% 8.84/9.06          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 8.84/9.06          | ~ (l1_pre_topc @ X26))),
% 8.84/9.06      inference('cnf', [status(esa)], [t48_tops_1])).
% 8.84/9.06  thf('20', plain,
% 8.84/9.06      (![X0 : $i, X1 : $i]:
% 8.84/9.06         (~ (l1_pre_topc @ sk_A)
% 8.84/9.06          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.84/9.06          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.84/9.06             (k1_tops_1 @ sk_A @ X1))
% 8.84/9.06          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 8.84/9.06      inference('sup-', [status(thm)], ['18', '19'])).
% 8.84/9.06  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 8.84/9.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.84/9.06  thf('22', plain,
% 8.84/9.06      (![X0 : $i, X1 : $i]:
% 8.84/9.06         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.84/9.06          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.84/9.06             (k1_tops_1 @ sk_A @ X1))
% 8.84/9.06          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 8.84/9.06      inference('demod', [status(thm)], ['20', '21'])).
% 8.84/9.06  thf('23', plain,
% 8.84/9.06      (![X0 : $i]:
% 8.84/9.06         (~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 8.84/9.06          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.84/9.06             (k1_tops_1 @ sk_A @ sk_B)))),
% 8.84/9.06      inference('sup-', [status(thm)], ['13', '22'])).
% 8.84/9.06  thf(t36_xboole_1, axiom,
% 8.84/9.06    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 8.84/9.06  thf('24', plain,
% 8.84/9.06      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 8.84/9.06      inference('cnf', [status(esa)], [t36_xboole_1])).
% 8.84/9.06  thf('25', plain,
% 8.84/9.06      (![X0 : $i]:
% 8.84/9.06         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.84/9.06          (k1_tops_1 @ sk_A @ sk_B))),
% 8.84/9.06      inference('demod', [status(thm)], ['23', '24'])).
% 8.84/9.06  thf('26', plain,
% 8.84/9.06      (![X0 : $i]:
% 8.84/9.06         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 8.84/9.06          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.84/9.06      inference('sup-', [status(thm)], ['14', '15'])).
% 8.84/9.06  thf(t44_tops_1, axiom,
% 8.84/9.06    (![A:$i]:
% 8.84/9.06     ( ( l1_pre_topc @ A ) =>
% 8.84/9.06       ( ![B:$i]:
% 8.84/9.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.84/9.06           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 8.84/9.06  thf('27', plain,
% 8.84/9.06      (![X23 : $i, X24 : $i]:
% 8.84/9.06         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 8.84/9.06          | (r1_tarski @ (k1_tops_1 @ X24 @ X23) @ X23)
% 8.84/9.06          | ~ (l1_pre_topc @ X24))),
% 8.84/9.06      inference('cnf', [status(esa)], [t44_tops_1])).
% 8.84/9.06  thf('28', plain,
% 8.84/9.06      (![X0 : $i]:
% 8.84/9.06         (~ (l1_pre_topc @ sk_A)
% 8.84/9.06          | (r1_tarski @ 
% 8.84/9.06             (k1_tops_1 @ sk_A @ 
% 8.84/9.06              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 8.84/9.06             (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)))),
% 8.84/9.06      inference('sup-', [status(thm)], ['26', '27'])).
% 8.84/9.06  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 8.84/9.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.84/9.06  thf('30', plain,
% 8.84/9.06      (![X0 : $i]:
% 8.84/9.06         (r1_tarski @ 
% 8.84/9.06          (k1_tops_1 @ sk_A @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 8.84/9.06          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 8.84/9.06      inference('demod', [status(thm)], ['28', '29'])).
% 8.84/9.06  thf('31', plain,
% 8.84/9.06      (![X0 : $i]:
% 8.84/9.06         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.84/9.06           = (k4_xboole_0 @ sk_B @ X0))),
% 8.84/9.06      inference('sup-', [status(thm)], ['1', '2'])).
% 8.84/9.06  thf('32', plain,
% 8.84/9.06      (![X0 : $i]:
% 8.84/9.06         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.84/9.06           = (k4_xboole_0 @ sk_B @ X0))),
% 8.84/9.06      inference('sup-', [status(thm)], ['1', '2'])).
% 8.84/9.06  thf('33', plain,
% 8.84/9.06      (![X0 : $i]:
% 8.84/9.06         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.84/9.06          (k4_xboole_0 @ sk_B @ X0))),
% 8.84/9.06      inference('demod', [status(thm)], ['30', '31', '32'])).
% 8.84/9.06  thf(t106_xboole_1, axiom,
% 8.84/9.06    (![A:$i,B:$i,C:$i]:
% 8.84/9.06     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 8.84/9.06       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 8.84/9.06  thf('34', plain,
% 8.84/9.06      (![X2 : $i, X3 : $i, X4 : $i]:
% 8.84/9.06         ((r1_xboole_0 @ X2 @ X4)
% 8.84/9.06          | ~ (r1_tarski @ X2 @ (k4_xboole_0 @ X3 @ X4)))),
% 8.84/9.06      inference('cnf', [status(esa)], [t106_xboole_1])).
% 8.84/9.06  thf('35', plain,
% 8.84/9.06      (![X0 : $i]:
% 8.84/9.06         (r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ X0)),
% 8.84/9.06      inference('sup-', [status(thm)], ['33', '34'])).
% 8.84/9.06  thf(symmetry_r1_xboole_0, axiom,
% 8.84/9.06    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 8.84/9.06  thf('36', plain,
% 8.84/9.06      (![X0 : $i, X1 : $i]:
% 8.84/9.06         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 8.84/9.06      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 8.84/9.06  thf('37', plain,
% 8.84/9.06      (![X0 : $i]:
% 8.84/9.06         (r1_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 8.84/9.06      inference('sup-', [status(thm)], ['35', '36'])).
% 8.84/9.06  thf(t83_xboole_1, axiom,
% 8.84/9.06    (![A:$i,B:$i]:
% 8.84/9.06     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 8.84/9.06  thf('38', plain,
% 8.84/9.06      (![X9 : $i, X10 : $i]:
% 8.84/9.06         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 8.84/9.06      inference('cnf', [status(esa)], [t83_xboole_1])).
% 8.84/9.06  thf('39', plain,
% 8.84/9.06      (![X0 : $i]:
% 8.84/9.06         ((k4_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))
% 8.84/9.06           = (X0))),
% 8.84/9.06      inference('sup-', [status(thm)], ['37', '38'])).
% 8.84/9.06  thf('40', plain,
% 8.84/9.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.84/9.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.84/9.06  thf('41', plain,
% 8.84/9.06      (![X15 : $i, X16 : $i, X17 : $i]:
% 8.84/9.06         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 8.84/9.06          | (m1_subset_1 @ (k7_subset_1 @ X16 @ X15 @ X17) @ 
% 8.84/9.06             (k1_zfmisc_1 @ X16)))),
% 8.84/9.06      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 8.84/9.06  thf('42', plain,
% 8.84/9.06      (![X0 : $i]:
% 8.84/9.06         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 8.84/9.06          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.84/9.06      inference('sup-', [status(thm)], ['40', '41'])).
% 8.84/9.06  thf('43', plain,
% 8.84/9.06      (![X23 : $i, X24 : $i]:
% 8.84/9.06         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 8.84/9.06          | (r1_tarski @ (k1_tops_1 @ X24 @ X23) @ X23)
% 8.84/9.06          | ~ (l1_pre_topc @ X24))),
% 8.84/9.06      inference('cnf', [status(esa)], [t44_tops_1])).
% 8.84/9.06  thf('44', plain,
% 8.84/9.06      (![X0 : $i]:
% 8.84/9.06         (~ (l1_pre_topc @ sk_A)
% 8.84/9.06          | (r1_tarski @ 
% 8.84/9.06             (k1_tops_1 @ sk_A @ 
% 8.84/9.06              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)) @ 
% 8.84/9.06             (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)))),
% 8.84/9.06      inference('sup-', [status(thm)], ['42', '43'])).
% 8.84/9.06  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 8.84/9.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.84/9.06  thf('46', plain,
% 8.84/9.06      (![X0 : $i]:
% 8.84/9.06         (r1_tarski @ 
% 8.84/9.06          (k1_tops_1 @ sk_A @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)) @ 
% 8.84/9.06          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 8.84/9.06      inference('demod', [status(thm)], ['44', '45'])).
% 8.84/9.06  thf('47', plain,
% 8.84/9.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.84/9.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.84/9.06  thf('48', plain,
% 8.84/9.06      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.84/9.06         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 8.84/9.06          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 8.84/9.06      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.84/9.06  thf('49', plain,
% 8.84/9.06      (![X0 : $i]:
% 8.84/9.06         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 8.84/9.06           = (k4_xboole_0 @ sk_C @ X0))),
% 8.84/9.06      inference('sup-', [status(thm)], ['47', '48'])).
% 8.84/9.06  thf('50', plain,
% 8.84/9.06      (![X0 : $i]:
% 8.84/9.06         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 8.84/9.06           = (k4_xboole_0 @ sk_C @ X0))),
% 8.84/9.06      inference('sup-', [status(thm)], ['47', '48'])).
% 8.84/9.06  thf('51', plain,
% 8.84/9.06      (![X0 : $i]:
% 8.84/9.06         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_C @ X0)) @ 
% 8.84/9.06          (k4_xboole_0 @ sk_C @ X0))),
% 8.84/9.06      inference('demod', [status(thm)], ['46', '49', '50'])).
% 8.84/9.06  thf('52', plain,
% 8.84/9.06      (![X2 : $i, X3 : $i, X4 : $i]:
% 8.84/9.06         ((r1_xboole_0 @ X2 @ X4)
% 8.84/9.06          | ~ (r1_tarski @ X2 @ (k4_xboole_0 @ X3 @ X4)))),
% 8.84/9.06      inference('cnf', [status(esa)], [t106_xboole_1])).
% 8.84/9.06  thf('53', plain,
% 8.84/9.06      (![X0 : $i]:
% 8.84/9.06         (r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_C @ X0)) @ X0)),
% 8.84/9.06      inference('sup-', [status(thm)], ['51', '52'])).
% 8.84/9.06  thf('54', plain,
% 8.84/9.06      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 8.84/9.06        (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 8.84/9.06      inference('sup+', [status(thm)], ['39', '53'])).
% 8.84/9.06  thf('55', plain,
% 8.84/9.06      (![X0 : $i, X1 : $i]:
% 8.84/9.06         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 8.84/9.06      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 8.84/9.06  thf('56', plain,
% 8.84/9.06      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 8.84/9.06        (k1_tops_1 @ sk_A @ sk_C))),
% 8.84/9.06      inference('sup-', [status(thm)], ['54', '55'])).
% 8.84/9.06  thf(t86_xboole_1, axiom,
% 8.84/9.06    (![A:$i,B:$i,C:$i]:
% 8.84/9.06     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 8.84/9.06       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 8.84/9.06  thf('57', plain,
% 8.84/9.06      (![X12 : $i, X13 : $i, X14 : $i]:
% 8.84/9.06         (~ (r1_tarski @ X12 @ X13)
% 8.84/9.06          | ~ (r1_xboole_0 @ X12 @ X14)
% 8.84/9.06          | (r1_tarski @ X12 @ (k4_xboole_0 @ X13 @ X14)))),
% 8.84/9.06      inference('cnf', [status(esa)], [t86_xboole_1])).
% 8.84/9.06  thf('58', plain,
% 8.84/9.06      (![X0 : $i]:
% 8.84/9.06         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 8.84/9.06           (k4_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))
% 8.84/9.06          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 8.84/9.06               X0))),
% 8.84/9.06      inference('sup-', [status(thm)], ['56', '57'])).
% 8.84/9.06  thf('59', plain,
% 8.84/9.06      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 8.84/9.06        (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 8.84/9.06      inference('sup-', [status(thm)], ['25', '58'])).
% 8.84/9.06  thf('60', plain, ($false), inference('demod', [status(thm)], ['12', '59'])).
% 8.84/9.06  
% 8.84/9.06  % SZS output end Refutation
% 8.84/9.06  
% 8.84/9.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

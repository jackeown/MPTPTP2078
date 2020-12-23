%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ee29utQun7

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:46 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 188 expanded)
%              Number of leaves         :   24 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  955 (3043 expanded)
%              Number of equality atoms :   31 (  47 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t32_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) @ ( k2_pre_topc @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) @ ( k2_pre_topc @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k7_subset_1 @ X17 @ X16 @ X18 )
        = ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k7_subset_1 @ X17 @ X16 @ X18 )
        = ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( k2_pre_topc @ A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k2_pre_topc @ X22 @ ( k4_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 @ X23 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k2_pre_topc @ X22 @ X21 ) @ ( k2_pre_topc @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t50_pre_topc])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k2_xboole_0 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('27',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ X0 )
        = ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['26','35'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X11 @ X10 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ X0 )
        = ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
      = ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k2_xboole_0 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_pre_topc @ sk_A @ ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_pre_topc @ sk_A @ ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
      = ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['52','61'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('63',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      | ~ ( r1_tarski @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k2_pre_topc @ sk_A @ ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_pre_topc @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['41','64'])).

thf('66',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['12','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ee29utQun7
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:58:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 1.59/1.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.59/1.78  % Solved by: fo/fo7.sh
% 1.59/1.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.59/1.78  % done 988 iterations in 1.337s
% 1.59/1.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.59/1.78  % SZS output start Refutation
% 1.59/1.78  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.59/1.78  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.59/1.78  thf(sk_C_type, type, sk_C: $i).
% 1.59/1.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.59/1.78  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.59/1.78  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.59/1.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.59/1.78  thf(sk_A_type, type, sk_A: $i).
% 1.59/1.78  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.59/1.78  thf(sk_B_type, type, sk_B: $i).
% 1.59/1.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.59/1.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.59/1.78  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.59/1.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.59/1.78  thf(t32_tops_1, conjecture,
% 1.59/1.78    (![A:$i]:
% 1.59/1.78     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.59/1.78       ( ![B:$i]:
% 1.59/1.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.59/1.78           ( ![C:$i]:
% 1.59/1.78             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.59/1.78               ( r1_tarski @
% 1.59/1.78                 ( k7_subset_1 @
% 1.59/1.78                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.59/1.78                   ( k2_pre_topc @ A @ C ) ) @ 
% 1.59/1.78                 ( k2_pre_topc @
% 1.59/1.78                   A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 1.59/1.78  thf(zf_stmt_0, negated_conjecture,
% 1.59/1.78    (~( ![A:$i]:
% 1.59/1.78        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.59/1.78          ( ![B:$i]:
% 1.59/1.78            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.59/1.78              ( ![C:$i]:
% 1.59/1.78                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.59/1.78                  ( r1_tarski @
% 1.59/1.78                    ( k7_subset_1 @
% 1.59/1.78                      ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.59/1.78                      ( k2_pre_topc @ A @ C ) ) @ 
% 1.59/1.78                    ( k2_pre_topc @
% 1.59/1.78                      A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) )),
% 1.59/1.78    inference('cnf.neg', [status(esa)], [t32_tops_1])).
% 1.59/1.78  thf('0', plain,
% 1.59/1.78      (~ (r1_tarski @ 
% 1.59/1.78          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.59/1.78           (k2_pre_topc @ sk_A @ sk_C)) @ 
% 1.59/1.78          (k2_pre_topc @ sk_A @ 
% 1.59/1.78           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)))),
% 1.59/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.78  thf('1', plain,
% 1.59/1.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.59/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.78  thf(redefinition_k7_subset_1, axiom,
% 1.59/1.78    (![A:$i,B:$i,C:$i]:
% 1.59/1.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.59/1.78       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.59/1.78  thf('2', plain,
% 1.59/1.78      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.59/1.78         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 1.59/1.78          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 1.59/1.78      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.59/1.78  thf('3', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.59/1.78           = (k4_xboole_0 @ sk_B @ X0))),
% 1.59/1.78      inference('sup-', [status(thm)], ['1', '2'])).
% 1.59/1.78  thf('4', plain,
% 1.59/1.78      (~ (r1_tarski @ 
% 1.59/1.78          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.59/1.78           (k2_pre_topc @ sk_A @ sk_C)) @ 
% 1.59/1.78          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.59/1.78      inference('demod', [status(thm)], ['0', '3'])).
% 1.59/1.78  thf('5', plain,
% 1.59/1.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.59/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.78  thf(dt_k2_pre_topc, axiom,
% 1.59/1.78    (![A:$i,B:$i]:
% 1.59/1.78     ( ( ( l1_pre_topc @ A ) & 
% 1.59/1.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.59/1.78       ( m1_subset_1 @
% 1.59/1.78         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.59/1.78  thf('6', plain,
% 1.59/1.78      (![X19 : $i, X20 : $i]:
% 1.59/1.78         (~ (l1_pre_topc @ X19)
% 1.59/1.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.59/1.78          | (m1_subset_1 @ (k2_pre_topc @ X19 @ X20) @ 
% 1.59/1.78             (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 1.59/1.78      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.59/1.78  thf('7', plain,
% 1.59/1.78      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.59/1.78         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.59/1.78        | ~ (l1_pre_topc @ sk_A))),
% 1.59/1.78      inference('sup-', [status(thm)], ['5', '6'])).
% 1.59/1.78  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 1.59/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.78  thf('9', plain,
% 1.59/1.78      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.59/1.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.59/1.78      inference('demod', [status(thm)], ['7', '8'])).
% 1.59/1.78  thf('10', plain,
% 1.59/1.78      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.59/1.78         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 1.59/1.78          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 1.59/1.78      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.59/1.78  thf('11', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.59/1.78           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.59/1.78      inference('sup-', [status(thm)], ['9', '10'])).
% 1.59/1.78  thf('12', plain,
% 1.59/1.78      (~ (r1_tarski @ 
% 1.59/1.78          (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.59/1.78           (k2_pre_topc @ sk_A @ sk_C)) @ 
% 1.59/1.78          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.59/1.78      inference('demod', [status(thm)], ['4', '11'])).
% 1.59/1.78  thf('13', plain,
% 1.59/1.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.59/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.78  thf('14', plain,
% 1.59/1.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.59/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.78  thf(t50_pre_topc, axiom,
% 1.59/1.78    (![A:$i]:
% 1.59/1.78     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.59/1.78       ( ![B:$i]:
% 1.59/1.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.59/1.78           ( ![C:$i]:
% 1.59/1.78             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.59/1.78               ( ( k2_pre_topc @
% 1.59/1.78                   A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) =
% 1.59/1.78                 ( k4_subset_1 @
% 1.59/1.78                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.59/1.78                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 1.59/1.78  thf('15', plain,
% 1.59/1.78      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.59/1.78         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.59/1.78          | ((k2_pre_topc @ X22 @ 
% 1.59/1.78              (k4_subset_1 @ (u1_struct_0 @ X22) @ X21 @ X23))
% 1.59/1.78              = (k4_subset_1 @ (u1_struct_0 @ X22) @ 
% 1.59/1.78                 (k2_pre_topc @ X22 @ X21) @ (k2_pre_topc @ X22 @ X23)))
% 1.59/1.78          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.59/1.78          | ~ (l1_pre_topc @ X22)
% 1.59/1.78          | ~ (v2_pre_topc @ X22))),
% 1.59/1.78      inference('cnf', [status(esa)], [t50_pre_topc])).
% 1.59/1.78  thf('16', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         (~ (v2_pre_topc @ sk_A)
% 1.59/1.78          | ~ (l1_pre_topc @ sk_A)
% 1.59/1.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.59/1.78          | ((k2_pre_topc @ sk_A @ 
% 1.59/1.78              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))
% 1.59/1.78              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.78                 (k2_pre_topc @ sk_A @ sk_C) @ (k2_pre_topc @ sk_A @ X0))))),
% 1.59/1.78      inference('sup-', [status(thm)], ['14', '15'])).
% 1.59/1.78  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 1.59/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.78  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 1.59/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.78  thf('19', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.59/1.78          | ((k2_pre_topc @ sk_A @ 
% 1.59/1.78              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))
% 1.59/1.78              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.78                 (k2_pre_topc @ sk_A @ sk_C) @ (k2_pre_topc @ sk_A @ X0))))),
% 1.59/1.78      inference('demod', [status(thm)], ['16', '17', '18'])).
% 1.59/1.78  thf('20', plain,
% 1.59/1.78      (((k2_pre_topc @ sk_A @ 
% 1.59/1.78         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B))
% 1.59/1.78         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 1.59/1.78            (k2_pre_topc @ sk_A @ sk_B)))),
% 1.59/1.78      inference('sup-', [status(thm)], ['13', '19'])).
% 1.59/1.78  thf('21', plain,
% 1.59/1.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.59/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.78  thf('22', plain,
% 1.59/1.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.59/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.78  thf(redefinition_k4_subset_1, axiom,
% 1.59/1.78    (![A:$i,B:$i,C:$i]:
% 1.59/1.78     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.59/1.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.59/1.78       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.59/1.78  thf('23', plain,
% 1.59/1.78      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.59/1.78         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 1.59/1.78          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 1.59/1.78          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 1.59/1.78      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.59/1.78  thf('24', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 1.59/1.78            = (k2_xboole_0 @ sk_C @ X0))
% 1.59/1.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.59/1.78      inference('sup-', [status(thm)], ['22', '23'])).
% 1.59/1.78  thf('25', plain,
% 1.59/1.78      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B)
% 1.59/1.78         = (k2_xboole_0 @ sk_C @ sk_B))),
% 1.59/1.78      inference('sup-', [status(thm)], ['21', '24'])).
% 1.59/1.78  thf('26', plain,
% 1.59/1.78      (((k2_pre_topc @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))
% 1.59/1.78         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 1.59/1.78            (k2_pre_topc @ sk_A @ sk_B)))),
% 1.59/1.78      inference('demod', [status(thm)], ['20', '25'])).
% 1.59/1.78  thf('27', plain,
% 1.59/1.78      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.59/1.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.59/1.78      inference('demod', [status(thm)], ['7', '8'])).
% 1.59/1.78  thf('28', plain,
% 1.59/1.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.59/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.78  thf('29', plain,
% 1.59/1.78      (![X19 : $i, X20 : $i]:
% 1.59/1.78         (~ (l1_pre_topc @ X19)
% 1.59/1.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.59/1.78          | (m1_subset_1 @ (k2_pre_topc @ X19 @ X20) @ 
% 1.59/1.78             (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 1.59/1.78      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.59/1.78  thf('30', plain,
% 1.59/1.78      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 1.59/1.78         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.59/1.78        | ~ (l1_pre_topc @ sk_A))),
% 1.59/1.78      inference('sup-', [status(thm)], ['28', '29'])).
% 1.59/1.78  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 1.59/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.78  thf('32', plain,
% 1.59/1.78      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 1.59/1.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.59/1.78      inference('demod', [status(thm)], ['30', '31'])).
% 1.59/1.78  thf('33', plain,
% 1.59/1.78      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.59/1.78         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 1.59/1.78          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 1.59/1.78          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 1.59/1.78      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.59/1.78  thf('34', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 1.59/1.78            X0) = (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_C) @ X0))
% 1.59/1.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.59/1.78      inference('sup-', [status(thm)], ['32', '33'])).
% 1.59/1.78  thf('35', plain,
% 1.59/1.78      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 1.59/1.78         (k2_pre_topc @ sk_A @ sk_B))
% 1.59/1.78         = (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 1.59/1.78            (k2_pre_topc @ sk_A @ sk_B)))),
% 1.59/1.78      inference('sup-', [status(thm)], ['27', '34'])).
% 1.59/1.78  thf('36', plain,
% 1.59/1.78      (((k2_pre_topc @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))
% 1.59/1.78         = (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 1.59/1.78            (k2_pre_topc @ sk_A @ sk_B)))),
% 1.59/1.78      inference('sup+', [status(thm)], ['26', '35'])).
% 1.59/1.78  thf(t36_xboole_1, axiom,
% 1.59/1.78    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.59/1.78  thf('37', plain,
% 1.59/1.78      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 1.59/1.78      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.59/1.78  thf(t44_xboole_1, axiom,
% 1.59/1.78    (![A:$i,B:$i,C:$i]:
% 1.59/1.78     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.59/1.78       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.59/1.78  thf('38', plain,
% 1.59/1.78      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.59/1.78         ((r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 1.59/1.78          | ~ (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9))),
% 1.59/1.78      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.59/1.78  thf('39', plain,
% 1.59/1.78      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.59/1.78      inference('sup-', [status(thm)], ['37', '38'])).
% 1.59/1.78  thf('40', plain,
% 1.59/1.78      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.59/1.78        (k2_pre_topc @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)))),
% 1.59/1.78      inference('sup+', [status(thm)], ['36', '39'])).
% 1.59/1.78  thf(t39_xboole_1, axiom,
% 1.59/1.78    (![A:$i,B:$i]:
% 1.59/1.78     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.59/1.78  thf('41', plain,
% 1.59/1.78      (![X2 : $i, X3 : $i]:
% 1.59/1.78         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 1.59/1.78           = (k2_xboole_0 @ X2 @ X3))),
% 1.59/1.78      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.59/1.78  thf('42', plain,
% 1.59/1.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.59/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.78  thf(dt_k7_subset_1, axiom,
% 1.59/1.78    (![A:$i,B:$i,C:$i]:
% 1.59/1.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.59/1.78       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.59/1.78  thf('43', plain,
% 1.59/1.78      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.59/1.78         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 1.59/1.78          | (m1_subset_1 @ (k7_subset_1 @ X11 @ X10 @ X12) @ 
% 1.59/1.78             (k1_zfmisc_1 @ X11)))),
% 1.59/1.78      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 1.59/1.78  thf('44', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 1.59/1.78          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.59/1.78      inference('sup-', [status(thm)], ['42', '43'])).
% 1.59/1.78  thf('45', plain,
% 1.59/1.78      (![X19 : $i, X20 : $i]:
% 1.59/1.78         (~ (l1_pre_topc @ X19)
% 1.59/1.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.59/1.78          | (m1_subset_1 @ (k2_pre_topc @ X19 @ X20) @ 
% 1.59/1.78             (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 1.59/1.78      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.59/1.78  thf('46', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         ((m1_subset_1 @ 
% 1.59/1.78           (k2_pre_topc @ sk_A @ 
% 1.59/1.78            (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 1.59/1.78           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.59/1.78          | ~ (l1_pre_topc @ sk_A))),
% 1.59/1.78      inference('sup-', [status(thm)], ['44', '45'])).
% 1.59/1.78  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 1.59/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.78  thf('48', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         (m1_subset_1 @ 
% 1.59/1.78          (k2_pre_topc @ sk_A @ 
% 1.59/1.78           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 1.59/1.78          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.59/1.78      inference('demod', [status(thm)], ['46', '47'])).
% 1.59/1.78  thf('49', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.59/1.78           = (k4_xboole_0 @ sk_B @ X0))),
% 1.59/1.78      inference('sup-', [status(thm)], ['1', '2'])).
% 1.59/1.78  thf('50', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 1.59/1.78          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.59/1.78      inference('demod', [status(thm)], ['48', '49'])).
% 1.59/1.78  thf('51', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 1.59/1.78            X0) = (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_C) @ X0))
% 1.59/1.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.59/1.78      inference('sup-', [status(thm)], ['32', '33'])).
% 1.59/1.78  thf('52', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 1.59/1.78           (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))
% 1.59/1.78           = (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 1.59/1.78              (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ X0))))),
% 1.59/1.78      inference('sup-', [status(thm)], ['50', '51'])).
% 1.59/1.78  thf('53', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 1.59/1.78          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.59/1.78      inference('sup-', [status(thm)], ['42', '43'])).
% 1.59/1.78  thf('54', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.59/1.78           = (k4_xboole_0 @ sk_B @ X0))),
% 1.59/1.78      inference('sup-', [status(thm)], ['1', '2'])).
% 1.59/1.78  thf('55', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 1.59/1.78          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.59/1.78      inference('demod', [status(thm)], ['53', '54'])).
% 1.59/1.78  thf('56', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.59/1.78          | ((k2_pre_topc @ sk_A @ 
% 1.59/1.78              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))
% 1.59/1.78              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.78                 (k2_pre_topc @ sk_A @ sk_C) @ (k2_pre_topc @ sk_A @ X0))))),
% 1.59/1.78      inference('demod', [status(thm)], ['16', '17', '18'])).
% 1.59/1.78  thf('57', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         ((k2_pre_topc @ sk_A @ 
% 1.59/1.78           (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.59/1.78            (k4_xboole_0 @ sk_B @ X0)))
% 1.59/1.78           = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.78              (k2_pre_topc @ sk_A @ sk_C) @ 
% 1.59/1.78              (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ X0))))),
% 1.59/1.78      inference('sup-', [status(thm)], ['55', '56'])).
% 1.59/1.78  thf('58', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 1.59/1.78          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.59/1.78      inference('demod', [status(thm)], ['53', '54'])).
% 1.59/1.78  thf('59', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 1.59/1.78            = (k2_xboole_0 @ sk_C @ X0))
% 1.59/1.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.59/1.78      inference('sup-', [status(thm)], ['22', '23'])).
% 1.59/1.78  thf('60', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.59/1.78           (k4_xboole_0 @ sk_B @ X0))
% 1.59/1.78           = (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ X0)))),
% 1.59/1.78      inference('sup-', [status(thm)], ['58', '59'])).
% 1.59/1.78  thf('61', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         ((k2_pre_topc @ sk_A @ 
% 1.59/1.78           (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ X0)))
% 1.59/1.78           = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.78              (k2_pre_topc @ sk_A @ sk_C) @ 
% 1.59/1.78              (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ X0))))),
% 1.59/1.78      inference('demod', [status(thm)], ['57', '60'])).
% 1.59/1.78  thf('62', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         ((k2_pre_topc @ sk_A @ 
% 1.59/1.78           (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ X0)))
% 1.59/1.78           = (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 1.59/1.78              (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ X0))))),
% 1.59/1.78      inference('sup+', [status(thm)], ['52', '61'])).
% 1.59/1.78  thf(t43_xboole_1, axiom,
% 1.59/1.78    (![A:$i,B:$i,C:$i]:
% 1.59/1.78     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.59/1.78       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.59/1.78  thf('63', plain,
% 1.59/1.78      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.59/1.78         ((r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 1.59/1.78          | ~ (r1_tarski @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 1.59/1.78      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.59/1.78  thf('64', plain,
% 1.59/1.78      (![X0 : $i, X1 : $i]:
% 1.59/1.78         (~ (r1_tarski @ X1 @ 
% 1.59/1.78             (k2_pre_topc @ sk_A @ 
% 1.59/1.78              (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ X0))))
% 1.59/1.78          | (r1_tarski @ (k4_xboole_0 @ X1 @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 1.59/1.78             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ X0))))),
% 1.59/1.78      inference('sup-', [status(thm)], ['62', '63'])).
% 1.59/1.78  thf('65', plain,
% 1.59/1.78      (![X0 : $i]:
% 1.59/1.78         (~ (r1_tarski @ X0 @ 
% 1.59/1.78             (k2_pre_topc @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)))
% 1.59/1.78          | (r1_tarski @ (k4_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 1.59/1.78             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 1.59/1.78      inference('sup-', [status(thm)], ['41', '64'])).
% 1.59/1.78  thf('66', plain,
% 1.59/1.78      ((r1_tarski @ 
% 1.59/1.78        (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.59/1.78         (k2_pre_topc @ sk_A @ sk_C)) @ 
% 1.59/1.78        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.59/1.78      inference('sup-', [status(thm)], ['40', '65'])).
% 1.59/1.78  thf('67', plain, ($false), inference('demod', [status(thm)], ['12', '66'])).
% 1.59/1.78  
% 1.59/1.78  % SZS output end Refutation
% 1.59/1.78  
% 1.62/1.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YvQOAnPtMm

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:46 EST 2020

% Result     : Theorem 2.26s
% Output     : Refutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 188 expanded)
%              Number of leaves         :   24 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          : 1072 (3050 expanded)
%              Number of equality atoms :   37 (  49 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k2_pre_topc @ X21 @ ( k4_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ X22 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k2_pre_topc @ X21 @ X20 ) @ ( k2_pre_topc @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t50_pre_topc])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
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
      | ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k4_subset_1 @ X13 @ X12 @ X14 )
        = ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('29',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('33',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k4_subset_1 @ X13 @ X12 @ X14 )
        = ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) )
    = ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['26','35'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('38',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('41',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X10 @ X9 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('50',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k4_subset_1 @ X13 @ X12 @ X14 )
        = ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ X0 )
        = ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
      = ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k2_pre_topc @ X21 @ ( k4_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ X22 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k2_pre_topc @ X21 @ X20 ) @ ( k2_pre_topc @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t50_pre_topc])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k4_subset_1 @ X13 @ X12 @ X14 )
        = ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k2_xboole_0 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_pre_topc @ sk_A @ ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_pre_topc @ sk_A @ ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
      = ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['52','68'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('70',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      | ~ ( r1_tarski @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k2_pre_topc @ sk_A @ ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_pre_topc @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['39','71'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_pre_topc @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['12','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YvQOAnPtMm
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:04:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.26/2.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.26/2.53  % Solved by: fo/fo7.sh
% 2.26/2.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.26/2.53  % done 1144 iterations in 2.080s
% 2.26/2.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.26/2.53  % SZS output start Refutation
% 2.26/2.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.26/2.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.26/2.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.26/2.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.26/2.53  thf(sk_A_type, type, sk_A: $i).
% 2.26/2.53  thf(sk_B_type, type, sk_B: $i).
% 2.26/2.53  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 2.26/2.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.26/2.53  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.26/2.53  thf(sk_C_type, type, sk_C: $i).
% 2.26/2.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.26/2.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.26/2.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.26/2.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.26/2.53  thf(t32_tops_1, conjecture,
% 2.26/2.53    (![A:$i]:
% 2.26/2.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.26/2.53       ( ![B:$i]:
% 2.26/2.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.26/2.53           ( ![C:$i]:
% 2.26/2.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.26/2.53               ( r1_tarski @
% 2.26/2.53                 ( k7_subset_1 @
% 2.26/2.53                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 2.26/2.53                   ( k2_pre_topc @ A @ C ) ) @ 
% 2.26/2.53                 ( k2_pre_topc @
% 2.26/2.53                   A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 2.26/2.53  thf(zf_stmt_0, negated_conjecture,
% 2.26/2.53    (~( ![A:$i]:
% 2.26/2.53        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.26/2.53          ( ![B:$i]:
% 2.26/2.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.26/2.53              ( ![C:$i]:
% 2.26/2.53                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.26/2.53                  ( r1_tarski @
% 2.26/2.53                    ( k7_subset_1 @
% 2.26/2.53                      ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 2.26/2.53                      ( k2_pre_topc @ A @ C ) ) @ 
% 2.26/2.53                    ( k2_pre_topc @
% 2.26/2.53                      A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) )),
% 2.26/2.53    inference('cnf.neg', [status(esa)], [t32_tops_1])).
% 2.26/2.53  thf('0', plain,
% 2.26/2.53      (~ (r1_tarski @ 
% 2.26/2.53          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.26/2.53           (k2_pre_topc @ sk_A @ sk_C)) @ 
% 2.26/2.53          (k2_pre_topc @ sk_A @ 
% 2.26/2.53           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)))),
% 2.26/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.53  thf('1', plain,
% 2.26/2.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.53  thf(redefinition_k7_subset_1, axiom,
% 2.26/2.53    (![A:$i,B:$i,C:$i]:
% 2.26/2.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.26/2.53       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 2.26/2.53  thf('2', plain,
% 2.26/2.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.26/2.53         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 2.26/2.53          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 2.26/2.53      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.26/2.53  thf('3', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.26/2.53           = (k4_xboole_0 @ sk_B @ X0))),
% 2.26/2.53      inference('sup-', [status(thm)], ['1', '2'])).
% 2.26/2.53  thf('4', plain,
% 2.26/2.53      (~ (r1_tarski @ 
% 2.26/2.53          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.26/2.53           (k2_pre_topc @ sk_A @ sk_C)) @ 
% 2.26/2.53          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 2.26/2.53      inference('demod', [status(thm)], ['0', '3'])).
% 2.26/2.53  thf('5', plain,
% 2.26/2.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.53  thf(dt_k2_pre_topc, axiom,
% 2.26/2.53    (![A:$i,B:$i]:
% 2.26/2.53     ( ( ( l1_pre_topc @ A ) & 
% 2.26/2.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.26/2.53       ( m1_subset_1 @
% 2.26/2.53         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.26/2.53  thf('6', plain,
% 2.26/2.53      (![X18 : $i, X19 : $i]:
% 2.26/2.53         (~ (l1_pre_topc @ X18)
% 2.26/2.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.26/2.53          | (m1_subset_1 @ (k2_pre_topc @ X18 @ X19) @ 
% 2.26/2.53             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 2.26/2.53      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 2.26/2.53  thf('7', plain,
% 2.26/2.53      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.26/2.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.26/2.53        | ~ (l1_pre_topc @ sk_A))),
% 2.26/2.53      inference('sup-', [status(thm)], ['5', '6'])).
% 2.26/2.53  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 2.26/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.53  thf('9', plain,
% 2.26/2.53      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.26/2.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.53      inference('demod', [status(thm)], ['7', '8'])).
% 2.26/2.53  thf('10', plain,
% 2.26/2.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.26/2.53         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 2.26/2.53          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 2.26/2.53      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.26/2.53  thf('11', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.26/2.53           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 2.26/2.53      inference('sup-', [status(thm)], ['9', '10'])).
% 2.26/2.53  thf('12', plain,
% 2.26/2.53      (~ (r1_tarski @ 
% 2.26/2.53          (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.26/2.53           (k2_pre_topc @ sk_A @ sk_C)) @ 
% 2.26/2.53          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 2.26/2.53      inference('demod', [status(thm)], ['4', '11'])).
% 2.26/2.53  thf('13', plain,
% 2.26/2.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.53  thf('14', plain,
% 2.26/2.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.53  thf(t50_pre_topc, axiom,
% 2.26/2.53    (![A:$i]:
% 2.26/2.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.26/2.53       ( ![B:$i]:
% 2.26/2.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.26/2.53           ( ![C:$i]:
% 2.26/2.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.26/2.53               ( ( k2_pre_topc @
% 2.26/2.53                   A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) =
% 2.26/2.53                 ( k4_subset_1 @
% 2.26/2.53                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 2.26/2.53                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 2.26/2.53  thf('15', plain,
% 2.26/2.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.26/2.53         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 2.26/2.53          | ((k2_pre_topc @ X21 @ 
% 2.26/2.53              (k4_subset_1 @ (u1_struct_0 @ X21) @ X20 @ X22))
% 2.26/2.53              = (k4_subset_1 @ (u1_struct_0 @ X21) @ 
% 2.26/2.53                 (k2_pre_topc @ X21 @ X20) @ (k2_pre_topc @ X21 @ X22)))
% 2.26/2.53          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 2.26/2.53          | ~ (l1_pre_topc @ X21)
% 2.26/2.53          | ~ (v2_pre_topc @ X21))),
% 2.26/2.53      inference('cnf', [status(esa)], [t50_pre_topc])).
% 2.26/2.53  thf('16', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         (~ (v2_pre_topc @ sk_A)
% 2.26/2.53          | ~ (l1_pre_topc @ sk_A)
% 2.26/2.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.26/2.53          | ((k2_pre_topc @ sk_A @ 
% 2.26/2.53              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))
% 2.26/2.53              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.26/2.53                 (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ X0))))),
% 2.26/2.53      inference('sup-', [status(thm)], ['14', '15'])).
% 2.26/2.53  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 2.26/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.53  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 2.26/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.53  thf('19', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.26/2.53          | ((k2_pre_topc @ sk_A @ 
% 2.26/2.53              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))
% 2.26/2.53              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.26/2.53                 (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ X0))))),
% 2.26/2.53      inference('demod', [status(thm)], ['16', '17', '18'])).
% 2.26/2.53  thf('20', plain,
% 2.26/2.53      (((k2_pre_topc @ sk_A @ 
% 2.26/2.53         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 2.26/2.53         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.26/2.53            (k2_pre_topc @ sk_A @ sk_C)))),
% 2.26/2.53      inference('sup-', [status(thm)], ['13', '19'])).
% 2.26/2.53  thf('21', plain,
% 2.26/2.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.53  thf('22', plain,
% 2.26/2.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.53  thf(redefinition_k4_subset_1, axiom,
% 2.26/2.53    (![A:$i,B:$i,C:$i]:
% 2.26/2.53     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.26/2.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.26/2.53       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 2.26/2.53  thf('23', plain,
% 2.26/2.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.26/2.53         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 2.26/2.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13))
% 2.26/2.53          | ((k4_subset_1 @ X13 @ X12 @ X14) = (k2_xboole_0 @ X12 @ X14)))),
% 2.26/2.53      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.26/2.53  thf('24', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.26/2.53            = (k2_xboole_0 @ sk_B @ X0))
% 2.26/2.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.53      inference('sup-', [status(thm)], ['22', '23'])).
% 2.26/2.53  thf('25', plain,
% 2.26/2.53      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 2.26/2.53         = (k2_xboole_0 @ sk_B @ sk_C))),
% 2.26/2.53      inference('sup-', [status(thm)], ['21', '24'])).
% 2.26/2.53  thf('26', plain,
% 2.26/2.53      (((k2_pre_topc @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 2.26/2.53         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.26/2.53            (k2_pre_topc @ sk_A @ sk_C)))),
% 2.26/2.53      inference('demod', [status(thm)], ['20', '25'])).
% 2.26/2.53  thf('27', plain,
% 2.26/2.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.53  thf('28', plain,
% 2.26/2.53      (![X18 : $i, X19 : $i]:
% 2.26/2.53         (~ (l1_pre_topc @ X18)
% 2.26/2.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.26/2.53          | (m1_subset_1 @ (k2_pre_topc @ X18 @ X19) @ 
% 2.26/2.53             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 2.26/2.53      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 2.26/2.53  thf('29', plain,
% 2.26/2.53      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 2.26/2.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.26/2.53        | ~ (l1_pre_topc @ sk_A))),
% 2.26/2.53      inference('sup-', [status(thm)], ['27', '28'])).
% 2.26/2.53  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 2.26/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.53  thf('31', plain,
% 2.26/2.53      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 2.26/2.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.53      inference('demod', [status(thm)], ['29', '30'])).
% 2.26/2.53  thf('32', plain,
% 2.26/2.53      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.26/2.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.53      inference('demod', [status(thm)], ['7', '8'])).
% 2.26/2.53  thf('33', plain,
% 2.26/2.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.26/2.53         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 2.26/2.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13))
% 2.26/2.53          | ((k4_subset_1 @ X13 @ X12 @ X14) = (k2_xboole_0 @ X12 @ X14)))),
% 2.26/2.53      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.26/2.53  thf('34', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.26/2.53            X0) = (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))
% 2.26/2.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.53      inference('sup-', [status(thm)], ['32', '33'])).
% 2.26/2.53  thf('35', plain,
% 2.26/2.53      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.26/2.53         (k2_pre_topc @ sk_A @ sk_C))
% 2.26/2.53         = (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.26/2.53            (k2_pre_topc @ sk_A @ sk_C)))),
% 2.26/2.53      inference('sup-', [status(thm)], ['31', '34'])).
% 2.26/2.53  thf('36', plain,
% 2.26/2.53      (((k2_pre_topc @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 2.26/2.53         = (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.26/2.53            (k2_pre_topc @ sk_A @ sk_C)))),
% 2.26/2.53      inference('sup+', [status(thm)], ['26', '35'])).
% 2.26/2.53  thf(t7_xboole_1, axiom,
% 2.26/2.53    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.26/2.53  thf('37', plain,
% 2.26/2.53      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 2.26/2.53      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.26/2.53  thf('38', plain,
% 2.26/2.53      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.26/2.53        (k2_pre_topc @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 2.26/2.53      inference('sup+', [status(thm)], ['36', '37'])).
% 2.26/2.53  thf(t39_xboole_1, axiom,
% 2.26/2.53    (![A:$i,B:$i]:
% 2.26/2.53     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.26/2.53  thf('39', plain,
% 2.26/2.53      (![X2 : $i, X3 : $i]:
% 2.26/2.53         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 2.26/2.53           = (k2_xboole_0 @ X2 @ X3))),
% 2.26/2.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.26/2.53  thf('40', plain,
% 2.26/2.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.53  thf(dt_k7_subset_1, axiom,
% 2.26/2.53    (![A:$i,B:$i,C:$i]:
% 2.26/2.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.26/2.53       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.26/2.53  thf('41', plain,
% 2.26/2.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.26/2.53         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 2.26/2.53          | (m1_subset_1 @ (k7_subset_1 @ X10 @ X9 @ X11) @ (k1_zfmisc_1 @ X10)))),
% 2.26/2.53      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 2.26/2.53  thf('42', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 2.26/2.53          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.53      inference('sup-', [status(thm)], ['40', '41'])).
% 2.26/2.53  thf('43', plain,
% 2.26/2.53      (![X18 : $i, X19 : $i]:
% 2.26/2.53         (~ (l1_pre_topc @ X18)
% 2.26/2.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.26/2.53          | (m1_subset_1 @ (k2_pre_topc @ X18 @ X19) @ 
% 2.26/2.53             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 2.26/2.53      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 2.26/2.53  thf('44', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         ((m1_subset_1 @ 
% 2.26/2.53           (k2_pre_topc @ sk_A @ 
% 2.26/2.53            (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 2.26/2.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.26/2.53          | ~ (l1_pre_topc @ sk_A))),
% 2.26/2.53      inference('sup-', [status(thm)], ['42', '43'])).
% 2.26/2.53  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 2.26/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.53  thf('46', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         (m1_subset_1 @ 
% 2.26/2.53          (k2_pre_topc @ sk_A @ 
% 2.26/2.53           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 2.26/2.53          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.53      inference('demod', [status(thm)], ['44', '45'])).
% 2.26/2.53  thf('47', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.26/2.53           = (k4_xboole_0 @ sk_B @ X0))),
% 2.26/2.53      inference('sup-', [status(thm)], ['1', '2'])).
% 2.26/2.53  thf('48', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 2.26/2.53          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.53      inference('demod', [status(thm)], ['46', '47'])).
% 2.26/2.53  thf('49', plain,
% 2.26/2.53      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 2.26/2.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.53      inference('demod', [status(thm)], ['29', '30'])).
% 2.26/2.53  thf('50', plain,
% 2.26/2.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.26/2.53         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 2.26/2.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13))
% 2.26/2.53          | ((k4_subset_1 @ X13 @ X12 @ X14) = (k2_xboole_0 @ X12 @ X14)))),
% 2.26/2.53      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.26/2.53  thf('51', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 2.26/2.53            X0) = (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_C) @ X0))
% 2.26/2.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.53      inference('sup-', [status(thm)], ['49', '50'])).
% 2.26/2.53  thf('52', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 2.26/2.53           (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))
% 2.26/2.53           = (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 2.26/2.53              (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ X0))))),
% 2.26/2.53      inference('sup-', [status(thm)], ['48', '51'])).
% 2.26/2.53  thf('53', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 2.26/2.53          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.53      inference('sup-', [status(thm)], ['40', '41'])).
% 2.26/2.53  thf('54', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 2.26/2.53           = (k4_xboole_0 @ sk_B @ X0))),
% 2.26/2.53      inference('sup-', [status(thm)], ['1', '2'])).
% 2.26/2.53  thf('55', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 2.26/2.53          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.53      inference('demod', [status(thm)], ['53', '54'])).
% 2.26/2.53  thf('56', plain,
% 2.26/2.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.53  thf('57', plain,
% 2.26/2.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.26/2.53         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 2.26/2.53          | ((k2_pre_topc @ X21 @ 
% 2.26/2.53              (k4_subset_1 @ (u1_struct_0 @ X21) @ X20 @ X22))
% 2.26/2.53              = (k4_subset_1 @ (u1_struct_0 @ X21) @ 
% 2.26/2.53                 (k2_pre_topc @ X21 @ X20) @ (k2_pre_topc @ X21 @ X22)))
% 2.26/2.53          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 2.26/2.53          | ~ (l1_pre_topc @ X21)
% 2.26/2.53          | ~ (v2_pre_topc @ X21))),
% 2.26/2.53      inference('cnf', [status(esa)], [t50_pre_topc])).
% 2.26/2.53  thf('58', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         (~ (v2_pre_topc @ sk_A)
% 2.26/2.53          | ~ (l1_pre_topc @ sk_A)
% 2.26/2.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.26/2.53          | ((k2_pre_topc @ sk_A @ 
% 2.26/2.53              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))
% 2.26/2.53              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.26/2.53                 (k2_pre_topc @ sk_A @ sk_C) @ (k2_pre_topc @ sk_A @ X0))))),
% 2.26/2.53      inference('sup-', [status(thm)], ['56', '57'])).
% 2.26/2.53  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 2.26/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.53  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 2.26/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.53  thf('61', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.26/2.53          | ((k2_pre_topc @ sk_A @ 
% 2.26/2.53              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))
% 2.26/2.53              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.26/2.53                 (k2_pre_topc @ sk_A @ sk_C) @ (k2_pre_topc @ sk_A @ X0))))),
% 2.26/2.53      inference('demod', [status(thm)], ['58', '59', '60'])).
% 2.26/2.53  thf('62', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         ((k2_pre_topc @ sk_A @ 
% 2.26/2.53           (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.26/2.53            (k4_xboole_0 @ sk_B @ X0)))
% 2.26/2.53           = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.26/2.53              (k2_pre_topc @ sk_A @ sk_C) @ 
% 2.26/2.53              (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ X0))))),
% 2.26/2.53      inference('sup-', [status(thm)], ['55', '61'])).
% 2.26/2.53  thf('63', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 2.26/2.53          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.53      inference('demod', [status(thm)], ['53', '54'])).
% 2.26/2.53  thf('64', plain,
% 2.26/2.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.53  thf('65', plain,
% 2.26/2.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.26/2.53         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 2.26/2.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13))
% 2.26/2.53          | ((k4_subset_1 @ X13 @ X12 @ X14) = (k2_xboole_0 @ X12 @ X14)))),
% 2.26/2.53      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.26/2.53  thf('66', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 2.26/2.53            = (k2_xboole_0 @ sk_C @ X0))
% 2.26/2.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.53      inference('sup-', [status(thm)], ['64', '65'])).
% 2.26/2.53  thf('67', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.26/2.53           (k4_xboole_0 @ sk_B @ X0))
% 2.26/2.53           = (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ X0)))),
% 2.26/2.53      inference('sup-', [status(thm)], ['63', '66'])).
% 2.26/2.53  thf('68', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         ((k2_pre_topc @ sk_A @ 
% 2.26/2.53           (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ X0)))
% 2.26/2.53           = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.26/2.53              (k2_pre_topc @ sk_A @ sk_C) @ 
% 2.26/2.53              (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ X0))))),
% 2.26/2.53      inference('demod', [status(thm)], ['62', '67'])).
% 2.26/2.53  thf('69', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         ((k2_pre_topc @ sk_A @ 
% 2.26/2.53           (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ X0)))
% 2.26/2.53           = (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 2.26/2.53              (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ X0))))),
% 2.26/2.53      inference('sup+', [status(thm)], ['52', '68'])).
% 2.26/2.53  thf(t43_xboole_1, axiom,
% 2.26/2.53    (![A:$i,B:$i,C:$i]:
% 2.26/2.53     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 2.26/2.53       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 2.26/2.53  thf('70', plain,
% 2.26/2.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.26/2.53         ((r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 2.26/2.53          | ~ (r1_tarski @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 2.26/2.53      inference('cnf', [status(esa)], [t43_xboole_1])).
% 2.26/2.53  thf('71', plain,
% 2.26/2.53      (![X0 : $i, X1 : $i]:
% 2.26/2.53         (~ (r1_tarski @ X1 @ 
% 2.26/2.53             (k2_pre_topc @ sk_A @ 
% 2.26/2.53              (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ X0))))
% 2.26/2.53          | (r1_tarski @ (k4_xboole_0 @ X1 @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 2.26/2.53             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ X0))))),
% 2.26/2.53      inference('sup-', [status(thm)], ['69', '70'])).
% 2.26/2.53  thf('72', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         (~ (r1_tarski @ X0 @ 
% 2.26/2.53             (k2_pre_topc @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)))
% 2.26/2.53          | (r1_tarski @ (k4_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 2.26/2.53             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 2.26/2.53      inference('sup-', [status(thm)], ['39', '71'])).
% 2.26/2.53  thf(commutativity_k2_xboole_0, axiom,
% 2.26/2.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.26/2.53  thf('73', plain,
% 2.26/2.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.26/2.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.26/2.53  thf('74', plain,
% 2.26/2.53      (![X0 : $i]:
% 2.26/2.53         (~ (r1_tarski @ X0 @ 
% 2.26/2.53             (k2_pre_topc @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 2.26/2.53          | (r1_tarski @ (k4_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 2.26/2.53             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 2.26/2.53      inference('demod', [status(thm)], ['72', '73'])).
% 2.26/2.53  thf('75', plain,
% 2.26/2.53      ((r1_tarski @ 
% 2.26/2.53        (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.26/2.53         (k2_pre_topc @ sk_A @ sk_C)) @ 
% 2.26/2.53        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 2.26/2.53      inference('sup-', [status(thm)], ['38', '74'])).
% 2.26/2.53  thf('76', plain, ($false), inference('demod', [status(thm)], ['12', '75'])).
% 2.26/2.53  
% 2.26/2.53  % SZS output end Refutation
% 2.26/2.53  
% 2.39/2.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

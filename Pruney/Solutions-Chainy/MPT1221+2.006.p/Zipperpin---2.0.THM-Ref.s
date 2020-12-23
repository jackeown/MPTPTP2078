%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H0fxWfq1Cu

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  145 (1344 expanded)
%              Number of leaves         :   36 ( 430 expanded)
%              Depth                    :   23
%              Number of atoms          : 1091 (11516 expanded)
%              Number of equality atoms :   65 ( 753 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t29_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_tops_1])).

thf('0',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['9','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','17'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('19',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('21',plain,
    ( ( r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('23',plain,(
    ! [X28: $i] :
      ( ( l1_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('29',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('31',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['9','16'])).

thf('32',plain,
    ( ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('34',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','35'])).

thf('37',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('38',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X11 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('39',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('40',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('42',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X19 @ X17 )
        = ( k9_subset_1 @ X18 @ X19 @ ( k3_subset_1 @ X18 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','35'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('49',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('50',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','17'])).

thf('52',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( m1_subset_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('55',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('56',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X16 @ X14 @ X15 )
        = ( k3_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','57'])).

thf('59',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['9','16'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('60',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('61',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('63',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('64',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('66',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['9','16'])).

thf('68',plain,
    ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('70',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('71',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['58','71'])).

thf('73',plain,
    ( ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['37','72'])).

thf('74',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('75',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('79',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v4_pre_topc @ X26 @ X27 )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k2_struct_0 @ X27 ) @ X26 ) @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('80',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,
    ( ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['75','83'])).

thf('85',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('87',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','17'])).

thf('88',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['76'])).

thf('89',plain,
    ( ( v3_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('92',plain,
    ( ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('94',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k2_struct_0 @ X27 ) @ X26 ) @ X27 )
      | ( v4_pre_topc @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('95',plain,
    ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['92','98'])).

thf('100',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('101',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['76'])).

thf('103',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['85','101','102'])).

thf('104',plain,(
    v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['84','103'])).

thf('105',plain,
    ( $false
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['1','36','104'])).

thf('106',plain,(
    ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['85','101'])).

thf('107',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['105','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H0fxWfq1Cu
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:19:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.59  % Solved by: fo/fo7.sh
% 0.20/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.59  % done 311 iterations in 0.132s
% 0.20/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.59  % SZS output start Refutation
% 0.20/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.59  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.59  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.59  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.59  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.59  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.59  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.59  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.59  thf(t29_tops_1, conjecture,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( l1_pre_topc @ A ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.59           ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.59             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.59    (~( ![A:$i]:
% 0.20/0.59        ( ( l1_pre_topc @ A ) =>
% 0.20/0.59          ( ![B:$i]:
% 0.20/0.59            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.59              ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.59                ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 0.20/0.59    inference('cnf.neg', [status(esa)], [t29_tops_1])).
% 0.20/0.59  thf('0', plain,
% 0.20/0.59      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.59        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('1', plain,
% 0.20/0.59      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.20/0.59         <= (~
% 0.20/0.59             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.59      inference('split', [status(esa)], ['0'])).
% 0.20/0.59  thf('2', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(d5_subset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.59       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.59  thf('3', plain,
% 0.20/0.59      (![X9 : $i, X10 : $i]:
% 0.20/0.59         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 0.20/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.20/0.59      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.59  thf('4', plain,
% 0.20/0.59      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.59  thf('5', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(t3_subset, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.59  thf('6', plain,
% 0.20/0.59      (![X22 : $i, X23 : $i]:
% 0.20/0.59         ((r1_tarski @ X22 @ X23) | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.59  thf('7', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.59  thf(t28_xboole_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.59  thf('8', plain,
% 0.20/0.59      (![X2 : $i, X3 : $i]:
% 0.20/0.59         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.20/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.59  thf('9', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.59  thf(commutativity_k2_tarski, axiom,
% 0.20/0.59    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.59  thf('10', plain,
% 0.20/0.59      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.20/0.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.59  thf(t12_setfam_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.59  thf('11', plain,
% 0.20/0.59      (![X20 : $i, X21 : $i]:
% 0.20/0.59         ((k1_setfam_1 @ (k2_tarski @ X20 @ X21)) = (k3_xboole_0 @ X20 @ X21))),
% 0.20/0.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.59  thf('12', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.59      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.59  thf('13', plain,
% 0.20/0.59      (![X20 : $i, X21 : $i]:
% 0.20/0.59         ((k1_setfam_1 @ (k2_tarski @ X20 @ X21)) = (k3_xboole_0 @ X20 @ X21))),
% 0.20/0.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.59  thf('14', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.59      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.59  thf(t100_xboole_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.59  thf('15', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.59  thf('16', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.59      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.59  thf('17', plain,
% 0.20/0.59      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.59      inference('sup+', [status(thm)], ['9', '16'])).
% 0.20/0.59  thf('18', plain,
% 0.20/0.59      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.59      inference('demod', [status(thm)], ['4', '17'])).
% 0.20/0.59  thf(d3_struct_0, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.59  thf('19', plain,
% 0.20/0.59      (![X25 : $i]:
% 0.20/0.59         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.20/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.59  thf('20', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.59  thf('21', plain,
% 0.20/0.59      (((r1_tarski @ sk_B @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.59      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.59  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(dt_l1_pre_topc, axiom,
% 0.20/0.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.59  thf('23', plain,
% 0.20/0.59      (![X28 : $i]: ((l1_struct_0 @ X28) | ~ (l1_pre_topc @ X28))),
% 0.20/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.59  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.59  thf('25', plain, ((r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['21', '24'])).
% 0.20/0.59  thf('26', plain,
% 0.20/0.59      (![X2 : $i, X3 : $i]:
% 0.20/0.59         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.20/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.59  thf('27', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)) = (sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.59  thf('28', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.59      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.59  thf('29', plain,
% 0.20/0.59      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.59      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.59  thf('30', plain,
% 0.20/0.59      (![X25 : $i]:
% 0.20/0.59         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.20/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.59  thf('31', plain,
% 0.20/0.59      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.59      inference('sup+', [status(thm)], ['9', '16'])).
% 0.20/0.59  thf('32', plain,
% 0.20/0.59      ((((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59          = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.59        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.59      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.59  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.59  thf('34', plain,
% 0.20/0.59      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.59      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.59  thf('35', plain,
% 0.20/0.59      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.59      inference('sup+', [status(thm)], ['29', '34'])).
% 0.20/0.59  thf('36', plain,
% 0.20/0.59      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.59      inference('demod', [status(thm)], ['18', '35'])).
% 0.20/0.59  thf('37', plain,
% 0.20/0.59      (![X25 : $i]:
% 0.20/0.59         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.20/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.59  thf(dt_k2_subset_1, axiom,
% 0.20/0.59    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.59  thf('38', plain,
% 0.20/0.59      (![X11 : $i]: (m1_subset_1 @ (k2_subset_1 @ X11) @ (k1_zfmisc_1 @ X11))),
% 0.20/0.59      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.59  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.59  thf('39', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.20/0.59      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.59  thf('40', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 0.20/0.59      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.59  thf('41', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(t32_subset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.59       ( ![C:$i]:
% 0.20/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.59           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.20/0.59             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.20/0.59  thf('42', plain,
% 0.20/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.20/0.59          | ((k7_subset_1 @ X18 @ X19 @ X17)
% 0.20/0.59              = (k9_subset_1 @ X18 @ X19 @ (k3_subset_1 @ X18 @ X17)))
% 0.20/0.59          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t32_subset_1])).
% 0.20/0.59  thf('43', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.59          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.20/0.59              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.20/0.59                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.59  thf('44', plain,
% 0.20/0.59      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.59      inference('demod', [status(thm)], ['18', '35'])).
% 0.20/0.59  thf('45', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.59          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.20/0.59              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.20/0.59                 (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.59      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.59  thf('46', plain,
% 0.20/0.59      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.59            (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['40', '45'])).
% 0.20/0.59  thf('47', plain,
% 0.20/0.59      (![X25 : $i]:
% 0.20/0.59         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.20/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.59  thf('48', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(dt_k3_subset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.59       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.59  thf('49', plain,
% 0.20/0.59      (![X12 : $i, X13 : $i]:
% 0.20/0.59         ((m1_subset_1 @ (k3_subset_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))
% 0.20/0.59          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.20/0.59      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.20/0.59  thf('50', plain,
% 0.20/0.59      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.59  thf('51', plain,
% 0.20/0.59      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.59      inference('demod', [status(thm)], ['4', '17'])).
% 0.20/0.59  thf('52', plain,
% 0.20/0.59      ((m1_subset_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.59  thf('53', plain,
% 0.20/0.59      (((m1_subset_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.59        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.59      inference('sup+', [status(thm)], ['47', '52'])).
% 0.20/0.59  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.59  thf('55', plain,
% 0.20/0.59      ((m1_subset_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.59  thf(redefinition_k9_subset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.59       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.59  thf('56', plain,
% 0.20/0.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.59         (((k9_subset_1 @ X16 @ X14 @ X15) = (k3_xboole_0 @ X14 @ X15))
% 0.20/0.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.20/0.59  thf('57', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.20/0.59           (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.59           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.59  thf('58', plain,
% 0.20/0.59      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.59            (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.59      inference('demod', [status(thm)], ['46', '57'])).
% 0.20/0.59  thf('59', plain,
% 0.20/0.59      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.59      inference('sup+', [status(thm)], ['9', '16'])).
% 0.20/0.59  thf(t48_xboole_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.59  thf('60', plain,
% 0.20/0.59      (![X4 : $i, X5 : $i]:
% 0.20/0.59         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.20/0.59           = (k3_xboole_0 @ X4 @ X5))),
% 0.20/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.59  thf('61', plain,
% 0.20/0.59      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.59         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.59         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.59      inference('sup+', [status(thm)], ['59', '60'])).
% 0.20/0.59  thf('62', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.59      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.59  thf('63', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 0.20/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.59  thf('64', plain,
% 0.20/0.59      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.59         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.20/0.59      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.20/0.59  thf('65', plain,
% 0.20/0.59      (![X4 : $i, X5 : $i]:
% 0.20/0.59         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.20/0.59           = (k3_xboole_0 @ X4 @ X5))),
% 0.20/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.59  thf('66', plain,
% 0.20/0.59      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.59            (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.59      inference('sup+', [status(thm)], ['64', '65'])).
% 0.20/0.59  thf('67', plain,
% 0.20/0.59      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.59      inference('sup+', [status(thm)], ['9', '16'])).
% 0.20/0.59  thf('68', plain,
% 0.20/0.59      (((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.59            (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.59      inference('demod', [status(thm)], ['66', '67'])).
% 0.20/0.59  thf('69', plain,
% 0.20/0.59      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.59      inference('sup+', [status(thm)], ['29', '34'])).
% 0.20/0.59  thf('70', plain,
% 0.20/0.59      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.59      inference('sup+', [status(thm)], ['29', '34'])).
% 0.20/0.59  thf('71', plain,
% 0.20/0.59      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.59            (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.59      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.20/0.59  thf('72', plain,
% 0.20/0.59      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.59      inference('sup+', [status(thm)], ['58', '71'])).
% 0.20/0.59  thf('73', plain,
% 0.20/0.59      ((((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.59        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.59      inference('sup+', [status(thm)], ['37', '72'])).
% 0.20/0.59  thf('74', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.59  thf('75', plain,
% 0.20/0.59      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.59      inference('demod', [status(thm)], ['73', '74'])).
% 0.20/0.59  thf('76', plain,
% 0.20/0.59      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('77', plain,
% 0.20/0.59      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.59      inference('split', [status(esa)], ['76'])).
% 0.20/0.59  thf('78', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(d6_pre_topc, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( l1_pre_topc @ A ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.59           ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.59             ( v3_pre_topc @
% 0.20/0.59               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 0.20/0.59               A ) ) ) ) ))).
% 0.20/0.59  thf('79', plain,
% 0.20/0.59      (![X26 : $i, X27 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.20/0.59          | ~ (v4_pre_topc @ X26 @ X27)
% 0.20/0.59          | (v3_pre_topc @ 
% 0.20/0.59             (k7_subset_1 @ (u1_struct_0 @ X27) @ (k2_struct_0 @ X27) @ X26) @ 
% 0.20/0.59             X27)
% 0.20/0.59          | ~ (l1_pre_topc @ X27))),
% 0.20/0.59      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.20/0.59  thf('80', plain,
% 0.20/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.59        | (v3_pre_topc @ 
% 0.20/0.59           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.59           sk_A)
% 0.20/0.59        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.59  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('82', plain,
% 0.20/0.59      (((v3_pre_topc @ 
% 0.20/0.59         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.59         sk_A)
% 0.20/0.59        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.59  thf('83', plain,
% 0.20/0.59      (((v3_pre_topc @ 
% 0.20/0.59         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.59         sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['77', '82'])).
% 0.20/0.59  thf('84', plain,
% 0.20/0.59      (((v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.20/0.59         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.59      inference('sup+', [status(thm)], ['75', '83'])).
% 0.20/0.59  thf('85', plain,
% 0.20/0.59      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.20/0.59       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.59      inference('split', [status(esa)], ['0'])).
% 0.20/0.59  thf('86', plain,
% 0.20/0.59      (![X25 : $i]:
% 0.20/0.59         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.20/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.59  thf('87', plain,
% 0.20/0.59      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.59      inference('demod', [status(thm)], ['4', '17'])).
% 0.20/0.59  thf('88', plain,
% 0.20/0.59      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.20/0.59         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.59      inference('split', [status(esa)], ['76'])).
% 0.20/0.59  thf('89', plain,
% 0.20/0.59      (((v3_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.20/0.59         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.59      inference('sup+', [status(thm)], ['87', '88'])).
% 0.20/0.59  thf('90', plain,
% 0.20/0.59      ((((v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.59         | ~ (l1_struct_0 @ sk_A)))
% 0.20/0.59         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.59      inference('sup+', [status(thm)], ['86', '89'])).
% 0.20/0.59  thf('91', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.59  thf('92', plain,
% 0.20/0.59      (((v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.20/0.59         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['90', '91'])).
% 0.20/0.59  thf('93', plain,
% 0.20/0.59      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.20/0.59         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.59      inference('demod', [status(thm)], ['73', '74'])).
% 0.20/0.59  thf('94', plain,
% 0.20/0.59      (![X26 : $i, X27 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.20/0.59          | ~ (v3_pre_topc @ 
% 0.20/0.59               (k7_subset_1 @ (u1_struct_0 @ X27) @ (k2_struct_0 @ X27) @ X26) @ 
% 0.20/0.59               X27)
% 0.20/0.59          | (v4_pre_topc @ X26 @ X27)
% 0.20/0.59          | ~ (l1_pre_topc @ X27))),
% 0.20/0.59      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.20/0.59  thf('95', plain,
% 0.20/0.59      ((~ (v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.59        | (v4_pre_topc @ sk_B @ sk_A)
% 0.20/0.59        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.59  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('97', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('98', plain,
% 0.20/0.59      ((~ (v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.59        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.20/0.59  thf('99', plain,
% 0.20/0.59      (((v4_pre_topc @ sk_B @ sk_A))
% 0.20/0.59         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['92', '98'])).
% 0.20/0.59  thf('100', plain,
% 0.20/0.59      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.59      inference('split', [status(esa)], ['0'])).
% 0.20/0.59  thf('101', plain,
% 0.20/0.59      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.20/0.59       ~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['99', '100'])).
% 0.20/0.59  thf('102', plain,
% 0.20/0.59      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.20/0.59       ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.59      inference('split', [status(esa)], ['76'])).
% 0.20/0.59  thf('103', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.59      inference('sat_resolution*', [status(thm)], ['85', '101', '102'])).
% 0.20/0.59  thf('104', plain,
% 0.20/0.59      ((v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.20/0.59      inference('simpl_trail', [status(thm)], ['84', '103'])).
% 0.20/0.59  thf('105', plain,
% 0.20/0.59      (($false)
% 0.20/0.59         <= (~
% 0.20/0.59             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['1', '36', '104'])).
% 0.20/0.59  thf('106', plain,
% 0.20/0.59      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.59      inference('sat_resolution*', [status(thm)], ['85', '101'])).
% 0.20/0.59  thf('107', plain, ($false),
% 0.20/0.59      inference('simpl_trail', [status(thm)], ['105', '106'])).
% 0.20/0.59  
% 0.20/0.59  % SZS output end Refutation
% 0.20/0.59  
% 0.20/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

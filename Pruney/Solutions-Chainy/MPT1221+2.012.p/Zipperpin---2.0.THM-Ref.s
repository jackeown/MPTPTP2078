%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fGDu3uhCVf

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 724 expanded)
%              Number of leaves         :   26 ( 223 expanded)
%              Depth                    :   20
%              Number of atoms          :  930 (6887 expanded)
%              Number of equality atoms :   43 ( 249 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('9',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('10',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('13',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('16',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('18',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','19'])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X17: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k7_subset_1 @ X12 @ X13 @ X11 )
        = ( k9_subset_1 @ X12 @ X13 @ ( k3_subset_1 @ X12 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','19'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('29',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','19'])).

thf('31',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['26','33'])).

thf('35',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('42',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('44',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('46',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('50',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X7 @ ( k3_subset_1 @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('51',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('53',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['35','36','39','54'])).

thf('56',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v4_pre_topc @ X15 @ X16 )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k2_struct_0 @ X16 ) @ X15 ) @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('60',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,
    ( ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['55','63'])).

thf('65',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('68',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['56'])).

thf('69',plain,
    ( ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('72',plain,
    ( ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['35','36','39','54'])).

thf('74',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k2_struct_0 @ X16 ) @ X15 ) @ X16 )
      | ( v4_pre_topc @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('75',plain,
    ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('81',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['56'])).

thf('83',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['65','81','82'])).

thf('84',plain,(
    v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['64','83'])).

thf('85',plain,
    ( $false
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['1','20','84'])).

thf('86',plain,(
    ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['65','81'])).

thf('87',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['85','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fGDu3uhCVf
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:59:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 142 iterations in 0.082s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.21/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(t29_tops_1, conjecture,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ( v4_pre_topc @ B @ A ) <=>
% 0.21/0.55             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i]:
% 0.21/0.55        ( ( l1_pre_topc @ A ) =>
% 0.21/0.55          ( ![B:$i]:
% 0.21/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55              ( ( v4_pre_topc @ B @ A ) <=>
% 0.21/0.55                ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t29_tops_1])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.21/0.55        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.21/0.55         <= (~
% 0.21/0.55             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d5_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X2 : $i, X3 : $i]:
% 0.21/0.55         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.21/0.55          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.21/0.55         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf(d3_struct_0, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X14 : $i]:
% 0.21/0.55         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.55      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.55  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(dt_l1_pre_topc, axiom,
% 0.21/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.55  thf('9', plain, (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.55  thf('10', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['7', '10'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X2 : $i, X3 : $i]:
% 0.21/0.55         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.21/0.55          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.21/0.55         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X14 : $i]:
% 0.21/0.55         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.21/0.55         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.21/0.55          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.21/0.55         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.21/0.55         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.55      inference('sup+', [status(thm)], ['13', '18'])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.21/0.55         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['4', '19'])).
% 0.21/0.55  thf(dt_k2_struct_0, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_struct_0 @ A ) =>
% 0.21/0.55       ( m1_subset_1 @
% 0.21/0.55         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X17 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (k2_struct_0 @ X17) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.55          | ~ (l1_struct_0 @ X17))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t32_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( ![C:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.21/0.55             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.21/0.55          | ((k7_subset_1 @ X12 @ X13 @ X11)
% 0.21/0.55              = (k9_subset_1 @ X12 @ X13 @ (k3_subset_1 @ X12 @ X11)))
% 0.21/0.55          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t32_subset_1])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.21/0.55              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.21/0.55                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.21/0.55         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['4', '19'])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.21/0.55              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.21/0.55                 (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.55      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(dt_k3_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (k3_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))
% 0.21/0.55          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.21/0.55         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['4', '19'])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.55  thf(redefinition_k9_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.55         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.21/0.55          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.21/0.55           (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.55           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.21/0.55              = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.55      inference('demod', [status(thm)], ['26', '33'])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      ((~ (l1_struct_0 @ sk_A)
% 0.21/0.55        | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.21/0.55            = (k3_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.55               (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['21', '34'])).
% 0.21/0.55  thf('36', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf(t48_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.21/0.55           = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.21/0.55           = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.55           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['37', '38'])).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['7', '10'])).
% 0.21/0.55  thf('41', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (k3_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))
% 0.21/0.55          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.21/0.55         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      (![X2 : $i, X3 : $i]:
% 0.21/0.55         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.21/0.55          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.55  thf('46', plain,
% 0.21/0.55      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.55         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.55         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.55            (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.21/0.55           = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.55  thf('48', plain,
% 0.21/0.55      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.55         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.55         = (k3_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['7', '10'])).
% 0.21/0.55  thf(involutiveness_k3_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      (![X6 : $i, X7 : $i]:
% 0.21/0.55         (((k3_subset_1 @ X7 @ (k3_subset_1 @ X7 @ X6)) = (X6))
% 0.21/0.55          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.55      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.55         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.21/0.55         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.55         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.55  thf('54', plain, (((k3_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) = (sk_B))),
% 0.21/0.55      inference('sup+', [status(thm)], ['48', '53'])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.21/0.55         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['35', '36', '39', '54'])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.21/0.55        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('57', plain,
% 0.21/0.55      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['56'])).
% 0.21/0.55  thf('58', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d6_pre_topc, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ( v4_pre_topc @ B @ A ) <=>
% 0.21/0.55             ( v3_pre_topc @
% 0.21/0.55               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 0.21/0.55               A ) ) ) ) ))).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      (![X15 : $i, X16 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.55          | ~ (v4_pre_topc @ X15 @ X16)
% 0.21/0.55          | (v3_pre_topc @ 
% 0.21/0.55             (k7_subset_1 @ (u1_struct_0 @ X16) @ (k2_struct_0 @ X16) @ X15) @ 
% 0.21/0.55             X16)
% 0.21/0.55          | ~ (l1_pre_topc @ X16))),
% 0.21/0.55      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.21/0.55  thf('60', plain,
% 0.21/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (v3_pre_topc @ 
% 0.21/0.55           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55           sk_A)
% 0.21/0.55        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.55  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('62', plain,
% 0.21/0.55      (((v3_pre_topc @ 
% 0.21/0.55         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55         sk_A)
% 0.21/0.55        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.55  thf('63', plain,
% 0.21/0.55      (((v3_pre_topc @ 
% 0.21/0.55         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.55         sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['57', '62'])).
% 0.21/0.55  thf('64', plain,
% 0.21/0.55      (((v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.21/0.55         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['55', '63'])).
% 0.21/0.55  thf('65', plain,
% 0.21/0.55      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.21/0.55       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('66', plain,
% 0.21/0.55      (![X14 : $i]:
% 0.21/0.55         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.55  thf('67', plain,
% 0.21/0.55      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.21/0.55         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('68', plain,
% 0.21/0.55      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.21/0.55         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['56'])).
% 0.21/0.55  thf('69', plain,
% 0.21/0.55      (((v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.21/0.55         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['67', '68'])).
% 0.21/0.55  thf('70', plain,
% 0.21/0.55      ((((v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.21/0.55         | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.55         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['66', '69'])).
% 0.21/0.55  thf('71', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf('72', plain,
% 0.21/0.55      (((v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.21/0.55         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['70', '71'])).
% 0.21/0.55  thf('73', plain,
% 0.21/0.55      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.21/0.55         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['35', '36', '39', '54'])).
% 0.21/0.55  thf('74', plain,
% 0.21/0.55      (![X15 : $i, X16 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.55          | ~ (v3_pre_topc @ 
% 0.21/0.55               (k7_subset_1 @ (u1_struct_0 @ X16) @ (k2_struct_0 @ X16) @ X15) @ 
% 0.21/0.55               X16)
% 0.21/0.55          | (v4_pre_topc @ X15 @ X16)
% 0.21/0.55          | ~ (l1_pre_topc @ X16))),
% 0.21/0.55      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.21/0.55  thf('75', plain,
% 0.21/0.55      ((~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (v4_pre_topc @ sk_B @ sk_A)
% 0.21/0.55        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.55  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('77', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('78', plain,
% 0.21/0.55      ((~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.21/0.55        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.21/0.55  thf('79', plain,
% 0.21/0.55      (((v4_pre_topc @ sk_B @ sk_A))
% 0.21/0.55         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['72', '78'])).
% 0.21/0.55  thf('80', plain,
% 0.21/0.55      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('81', plain,
% 0.21/0.55      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.21/0.55       ~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['79', '80'])).
% 0.21/0.55  thf('82', plain,
% 0.21/0.55      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.21/0.55       ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.21/0.55      inference('split', [status(esa)], ['56'])).
% 0.21/0.55  thf('83', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['65', '81', '82'])).
% 0.21/0.55  thf('84', plain,
% 0.21/0.55      ((v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['64', '83'])).
% 0.21/0.55  thf('85', plain,
% 0.21/0.55      (($false)
% 0.21/0.55         <= (~
% 0.21/0.55             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['1', '20', '84'])).
% 0.21/0.55  thf('86', plain,
% 0.21/0.55      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['65', '81'])).
% 0.21/0.55  thf('87', plain, ($false),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['85', '86'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vcacbnbBSR

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:38 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 236 expanded)
%              Number of leaves         :   30 (  84 expanded)
%              Depth                    :   10
%              Number of atoms          :  627 (2456 expanded)
%              Number of equality atoms :   27 (  73 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t96_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t96_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X1 @ X2 )
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(t95_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
           => ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v3_tops_1 @ ( k2_tops_1 @ X19 @ X18 ) @ X19 )
      | ~ ( v3_pre_topc @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t95_tops_1])).

thf('8',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t62_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( k2_tops_1 @ X17 @ X16 )
        = ( k2_tops_1 @ X17 @ ( k3_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('17',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['11','17'])).

thf('19',plain,(
    ~ ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(t18_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) )
            = ( k2_struct_0 @ A ) ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X15 ) @ X14 @ ( k3_subset_1 @ ( u1_struct_0 @ X15 ) @ X14 ) )
        = ( k2_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t18_pre_topc])).

thf('23',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('25',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('28',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X1 @ X2 )
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('29',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_subset_1 @ X9 @ X10 @ ( k3_subset_1 @ X9 @ X10 ) )
        = ( k2_subset_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_subset_1 @ X9 @ X10 @ ( k3_subset_1 @ X9 @ X10 ) )
        = X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('36',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26','29','36'])).

thf('38',plain,(
    ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['20','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v4_pre_topc @ X11 @ X12 )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k2_struct_0 @ X12 ) @ X11 ) @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26','29','36'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('46',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('48',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('49',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( ( k7_subset_1 @ X7 @ X6 @ X8 )
        = ( k4_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['44','45','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['38','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vcacbnbBSR
% 0.11/0.32  % Computer   : n006.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 10:04:38 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.32  % Number of cores: 8
% 0.11/0.32  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.19/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.52  % Solved by: fo/fo7.sh
% 0.19/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.52  % done 96 iterations in 0.082s
% 0.19/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.52  % SZS output start Refutation
% 0.19/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.19/0.52  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.19/0.52  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.52  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.19/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.19/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.52  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.19/0.52  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.19/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.52  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.19/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.52  thf(t96_tops_1, conjecture,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52           ( ( v4_pre_topc @ B @ A ) =>
% 0.19/0.52             ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) ))).
% 0.19/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.52    (~( ![A:$i]:
% 0.19/0.52        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.52          ( ![B:$i]:
% 0.19/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52              ( ( v4_pre_topc @ B @ A ) =>
% 0.19/0.52                ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) ) )),
% 0.19/0.52    inference('cnf.neg', [status(esa)], [t96_tops_1])).
% 0.19/0.52  thf('0', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(dt_k3_subset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.52       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.52  thf('1', plain,
% 0.19/0.52      (![X4 : $i, X5 : $i]:
% 0.19/0.52         ((m1_subset_1 @ (k3_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))
% 0.19/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.19/0.52      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.19/0.52  thf('2', plain,
% 0.19/0.52      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.52  thf('3', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(d5_subset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.52       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.19/0.52  thf('4', plain,
% 0.19/0.52      (![X1 : $i, X2 : $i]:
% 0.19/0.52         (((k3_subset_1 @ X1 @ X2) = (k4_xboole_0 @ X1 @ X2))
% 0.19/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.19/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.52  thf('5', plain,
% 0.19/0.52      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.19/0.52         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.19/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.52  thf('6', plain,
% 0.19/0.52      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['2', '5'])).
% 0.19/0.52  thf(t95_tops_1, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52           ( ( v3_pre_topc @ B @ A ) =>
% 0.19/0.52             ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) ))).
% 0.19/0.52  thf('7', plain,
% 0.19/0.52      (![X18 : $i, X19 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.52          | (v3_tops_1 @ (k2_tops_1 @ X19 @ X18) @ X19)
% 0.19/0.52          | ~ (v3_pre_topc @ X18 @ X19)
% 0.19/0.52          | ~ (l1_pre_topc @ X19)
% 0.19/0.52          | ~ (v2_pre_topc @ X19))),
% 0.19/0.52      inference('cnf', [status(esa)], [t95_tops_1])).
% 0.19/0.52  thf('8', plain,
% 0.19/0.52      ((~ (v2_pre_topc @ sk_A)
% 0.19/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.52        | ~ (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.19/0.52        | (v3_tops_1 @ 
% 0.19/0.52           (k2_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.19/0.52           sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.52  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('11', plain,
% 0.19/0.52      ((~ (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.19/0.52        | (v3_tops_1 @ 
% 0.19/0.52           (k2_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.19/0.52           sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.19/0.52  thf('12', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(t62_tops_1, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( l1_pre_topc @ A ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52           ( ( k2_tops_1 @ A @ B ) =
% 0.19/0.52             ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.19/0.52  thf('13', plain,
% 0.19/0.52      (![X16 : $i, X17 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.19/0.52          | ((k2_tops_1 @ X17 @ X16)
% 0.19/0.52              = (k2_tops_1 @ X17 @ (k3_subset_1 @ (u1_struct_0 @ X17) @ X16)))
% 0.19/0.52          | ~ (l1_pre_topc @ X17))),
% 0.19/0.52      inference('cnf', [status(esa)], [t62_tops_1])).
% 0.19/0.52  thf('14', plain,
% 0.19/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.52        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.52            = (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.52  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('16', plain,
% 0.19/0.52      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.19/0.52         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.19/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.52  thf('17', plain,
% 0.19/0.52      (((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.52         = (k2_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.52      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.19/0.52  thf('18', plain,
% 0.19/0.52      ((~ (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.19/0.52        | (v3_tops_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['11', '17'])).
% 0.19/0.52  thf('19', plain, (~ (v3_tops_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('20', plain,
% 0.19/0.52      (~ (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.19/0.52      inference('clc', [status(thm)], ['18', '19'])).
% 0.19/0.52  thf('21', plain,
% 0.19/0.52      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['2', '5'])).
% 0.19/0.52  thf(t18_pre_topc, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( l1_struct_0 @ A ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52           ( ( k4_subset_1 @
% 0.19/0.52               ( u1_struct_0 @ A ) @ B @ 
% 0.19/0.52               ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.19/0.52             ( k2_struct_0 @ A ) ) ) ) ))).
% 0.19/0.52  thf('22', plain,
% 0.19/0.52      (![X14 : $i, X15 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.19/0.52          | ((k4_subset_1 @ (u1_struct_0 @ X15) @ X14 @ 
% 0.19/0.52              (k3_subset_1 @ (u1_struct_0 @ X15) @ X14)) = (k2_struct_0 @ X15))
% 0.19/0.52          | ~ (l1_struct_0 @ X15))),
% 0.19/0.52      inference('cnf', [status(esa)], [t18_pre_topc])).
% 0.19/0.52  thf('23', plain,
% 0.19/0.52      ((~ (l1_struct_0 @ sk_A)
% 0.19/0.52        | ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.52            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.52            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.52             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.19/0.52            = (k2_struct_0 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.52  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(dt_l1_pre_topc, axiom,
% 0.19/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.52  thf('25', plain,
% 0.19/0.52      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.19/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.52  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.52  thf('27', plain,
% 0.19/0.52      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['2', '5'])).
% 0.19/0.52  thf('28', plain,
% 0.19/0.52      (![X1 : $i, X2 : $i]:
% 0.19/0.52         (((k3_subset_1 @ X1 @ X2) = (k4_xboole_0 @ X1 @ X2))
% 0.19/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.19/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.52  thf('29', plain,
% 0.19/0.52      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.52         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.52         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.52            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.52  thf('30', plain,
% 0.19/0.52      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['2', '5'])).
% 0.19/0.52  thf(t25_subset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.52       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.19/0.52         ( k2_subset_1 @ A ) ) ))).
% 0.19/0.52  thf('31', plain,
% 0.19/0.52      (![X9 : $i, X10 : $i]:
% 0.19/0.52         (((k4_subset_1 @ X9 @ X10 @ (k3_subset_1 @ X9 @ X10))
% 0.19/0.52            = (k2_subset_1 @ X9))
% 0.19/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.19/0.52  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.52  thf('32', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.19/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.52  thf('33', plain,
% 0.19/0.52      (![X9 : $i, X10 : $i]:
% 0.19/0.52         (((k4_subset_1 @ X9 @ X10 @ (k3_subset_1 @ X9 @ X10)) = (X9))
% 0.19/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.19/0.52      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.52  thf('34', plain,
% 0.19/0.52      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.52         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.52         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.52          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.19/0.52         = (u1_struct_0 @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['30', '33'])).
% 0.19/0.52  thf('35', plain,
% 0.19/0.52      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.52         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.52         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.52            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.52  thf('36', plain,
% 0.19/0.52      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.52         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.52         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.52          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.19/0.52         = (u1_struct_0 @ sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['34', '35'])).
% 0.19/0.52  thf('37', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['23', '26', '29', '36'])).
% 0.19/0.52  thf('38', plain,
% 0.19/0.52      (~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.19/0.52      inference('demod', [status(thm)], ['20', '37'])).
% 0.19/0.52  thf('39', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(d6_pre_topc, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( l1_pre_topc @ A ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52           ( ( v4_pre_topc @ B @ A ) <=>
% 0.19/0.52             ( v3_pre_topc @
% 0.19/0.52               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 0.19/0.52               A ) ) ) ) ))).
% 0.19/0.52  thf('40', plain,
% 0.19/0.52      (![X11 : $i, X12 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.19/0.52          | ~ (v4_pre_topc @ X11 @ X12)
% 0.19/0.52          | (v3_pre_topc @ 
% 0.19/0.52             (k7_subset_1 @ (u1_struct_0 @ X12) @ (k2_struct_0 @ X12) @ X11) @ 
% 0.19/0.52             X12)
% 0.19/0.52          | ~ (l1_pre_topc @ X12))),
% 0.19/0.52      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.19/0.52  thf('41', plain,
% 0.19/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.52        | (v3_pre_topc @ 
% 0.19/0.52           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.52           sk_A)
% 0.19/0.52        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.52  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('43', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('44', plain,
% 0.19/0.52      ((v3_pre_topc @ 
% 0.19/0.52        (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.52        sk_A)),
% 0.19/0.52      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.19/0.52  thf('45', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['23', '26', '29', '36'])).
% 0.19/0.52  thf(dt_k2_subset_1, axiom,
% 0.19/0.52    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.52  thf('46', plain,
% 0.19/0.52      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.19/0.52      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.19/0.52  thf('47', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.19/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.52  thf('48', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.19/0.52      inference('demod', [status(thm)], ['46', '47'])).
% 0.19/0.52  thf(redefinition_k7_subset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.52       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.19/0.52  thf('49', plain,
% 0.19/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.19/0.52          | ((k7_subset_1 @ X7 @ X6 @ X8) = (k4_xboole_0 @ X6 @ X8)))),
% 0.19/0.52      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.19/0.52  thf('50', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.19/0.52  thf('51', plain,
% 0.19/0.52      ((v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.19/0.52      inference('demod', [status(thm)], ['44', '45', '50'])).
% 0.19/0.52  thf('52', plain, ($false), inference('demod', [status(thm)], ['38', '51'])).
% 0.19/0.52  
% 0.19/0.52  % SZS output end Refutation
% 0.19/0.52  
% 0.36/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

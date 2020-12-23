%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VyTeBcJjKy

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 133 expanded)
%              Number of leaves         :   26 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  509 (1334 expanded)
%              Number of equality atoms :   12 (  22 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(t43_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( ( ( k1_tops_1 @ X16 @ ( k2_struct_0 @ X16 ) )
        = ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t43_tops_1])).

thf(t35_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_connsp_2])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X5 @ X4 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    r1_tarski @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) )
      | ( ( k4_subset_1 @ X8 @ X7 @ X9 )
        = ( k2_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) )
            = ( k2_struct_0 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X15 ) @ X14 @ ( k3_subset_1 @ ( u1_struct_0 @ X15 ) @ X14 ) )
        = ( k2_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t18_pre_topc])).

thf('18',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('20',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','21','22'])).

thf('24',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','23'])).

thf('25',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m2_connsp_2 @ C @ A @ B )
              <=> ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r1_tarski @ X17 @ ( k1_tops_1 @ X18 @ X19 ) )
      | ( m2_connsp_2 @ X19 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ~ ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','35'])).

thf('37',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','21','22'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('39',plain,(
    r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['36','39','40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VyTeBcJjKy
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:56:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 135 iterations in 0.071s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.53  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.22/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.53  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.22/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.53  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.22/0.53  thf(t43_tops_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.53       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      (![X16 : $i]:
% 0.22/0.53         (((k1_tops_1 @ X16 @ (k2_struct_0 @ X16)) = (k2_struct_0 @ X16))
% 0.22/0.53          | ~ (l1_pre_topc @ X16)
% 0.22/0.53          | ~ (v2_pre_topc @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [t43_tops_1])).
% 0.22/0.53  thf(t35_connsp_2, conjecture,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.53           ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i]:
% 0.22/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.53            ( l1_pre_topc @ A ) ) =>
% 0.22/0.53          ( ![B:$i]:
% 0.22/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.53              ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t35_connsp_2])).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(dt_k3_subset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.53       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (![X2 : $i, X3 : $i]:
% 0.22/0.53         ((m1_subset_1 @ (k3_subset_1 @ X2 @ X3) @ (k1_zfmisc_1 @ X2))
% 0.22/0.53          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.22/0.53      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(dt_k4_subset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.22/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.53       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.22/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5))
% 0.22/0.53          | (m1_subset_1 @ (k4_subset_1 @ X5 @ X4 @ X6) @ (k1_zfmisc_1 @ X5)))),
% 0.22/0.53      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.22/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      ((m1_subset_1 @ 
% 0.22/0.53        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.53         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.22/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['3', '6'])).
% 0.22/0.53  thf(t3_subset, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      (![X10 : $i, X11 : $i]:
% 0.22/0.53         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      ((r1_tarski @ 
% 0.22/0.53        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.53         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.22/0.53        (u1_struct_0 @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.53  thf('11', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(redefinition_k4_subset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.22/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.53       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.22/0.53          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8))
% 0.22/0.53          | ((k4_subset_1 @ X8 @ X7 @ X9) = (k2_xboole_0 @ X7 @ X9)))),
% 0.22/0.53      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.22/0.53  thf('13', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.22/0.53            = (k2_xboole_0 @ sk_B @ X0))
% 0.22/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.53         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.53         = (k2_xboole_0 @ sk_B @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['10', '13'])).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      ((r1_tarski @ 
% 0.22/0.53        (k2_xboole_0 @ sk_B @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.22/0.53        (u1_struct_0 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['9', '14'])).
% 0.22/0.53  thf('16', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t18_pre_topc, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_struct_0 @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( ( k4_subset_1 @
% 0.22/0.54               ( u1_struct_0 @ A ) @ B @ 
% 0.22/0.54               ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.22/0.54             ( k2_struct_0 @ A ) ) ) ) ))).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      (![X14 : $i, X15 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.22/0.54          | ((k4_subset_1 @ (u1_struct_0 @ X15) @ X14 @ 
% 0.22/0.54              (k3_subset_1 @ (u1_struct_0 @ X15) @ X14)) = (k2_struct_0 @ X15))
% 0.22/0.54          | ~ (l1_struct_0 @ X15))),
% 0.22/0.54      inference('cnf', [status(esa)], [t18_pre_topc])).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      ((~ (l1_struct_0 @ sk_A)
% 0.22/0.54        | ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.54            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (k2_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.54  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(dt_l1_pre_topc, axiom,
% 0.22/0.54    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.54  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.54         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.54         = (k2_xboole_0 @ sk_B @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['10', '13'])).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.54         = (k2_struct_0 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['18', '21', '22'])).
% 0.22/0.54  thf('24', plain, ((r1_tarski @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['15', '23'])).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      (![X10 : $i, X12 : $i]:
% 0.22/0.54         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.54  thf('26', plain,
% 0.22/0.54      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.54  thf('27', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(d2_connsp_2, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54           ( ![C:$i]:
% 0.22/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.54               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.22/0.54                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.22/0.54  thf('28', plain,
% 0.22/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.54          | ~ (r1_tarski @ X17 @ (k1_tops_1 @ X18 @ X19))
% 0.22/0.54          | (m2_connsp_2 @ X19 @ X18 @ X17)
% 0.22/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.54          | ~ (l1_pre_topc @ X18)
% 0.22/0.54          | ~ (v2_pre_topc @ X18))),
% 0.22/0.54      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (v2_pre_topc @ sk_A)
% 0.22/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.22/0.54          | ~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.54  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.54          | (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.22/0.54          | ~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.22/0.54        | (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['26', '32'])).
% 0.22/0.54  thf('34', plain, (~ (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('35', plain,
% 0.22/0.54      (~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.22/0.54      inference('clc', [status(thm)], ['33', '34'])).
% 0.22/0.54  thf('36', plain,
% 0.22/0.54      ((~ (r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))
% 0.22/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['0', '35'])).
% 0.22/0.54  thf('37', plain,
% 0.22/0.54      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.54         = (k2_struct_0 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['18', '21', '22'])).
% 0.22/0.54  thf(t7_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.54  thf('38', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.54      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.54  thf('39', plain, ((r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))),
% 0.22/0.54      inference('sup+', [status(thm)], ['37', '38'])).
% 0.22/0.54  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('42', plain, ($false),
% 0.22/0.54      inference('demod', [status(thm)], ['36', '39', '40', '41'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

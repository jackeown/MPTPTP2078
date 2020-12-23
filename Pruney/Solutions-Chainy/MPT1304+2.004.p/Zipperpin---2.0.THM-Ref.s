%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u4NPPFeQ0u

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:21 EST 2020

% Result     : Theorem 16.20s
% Output     : Refutation 16.20s
% Verified   : 
% Statistics : Number of formulae       :   63 (  98 expanded)
%              Number of leaves         :   25 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  444 ( 889 expanded)
%              Number of equality atoms :   11 (  25 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t22_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( v1_tops_2 @ B @ A )
               => ( v1_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( v1_tops_2 @ B @ A )
                 => ( v1_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_tops_2])).

thf('0',plain,(
    ~ ( v1_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( ( k7_subset_1 @ X42 @ X41 @ X43 )
        = ( k4_xboole_0 @ X41 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k3_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X7 ) ) @ X6 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t110_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k5_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['18','21'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','24'])).

thf('26',plain,(
    ! [X46: $i,X48: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X48 ) )
      | ~ ( r1_tarski @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t18_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( r1_tarski @ B @ C )
                  & ( v1_tops_2 @ C @ A ) )
               => ( v1_tops_2 @ B @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) ) )
      | ( v1_tops_2 @ X49 @ X50 )
      | ~ ( r1_tarski @ X49 @ X51 )
      | ~ ( v1_tops_2 @ X51 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) ) )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[t18_tops_2])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('34',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['4','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u4NPPFeQ0u
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 16.20/16.42  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 16.20/16.42  % Solved by: fo/fo7.sh
% 16.20/16.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 16.20/16.42  % done 3755 iterations in 15.964s
% 16.20/16.42  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 16.20/16.42  % SZS output start Refutation
% 16.20/16.42  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 16.20/16.42  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 16.20/16.42  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 16.20/16.42  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 16.20/16.42  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 16.20/16.42  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 16.20/16.42  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 16.20/16.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 16.20/16.42  thf(sk_B_type, type, sk_B: $i).
% 16.20/16.42  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 16.20/16.42  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 16.20/16.42  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 16.20/16.42  thf(sk_C_type, type, sk_C: $i).
% 16.20/16.42  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 16.20/16.42  thf(sk_A_type, type, sk_A: $i).
% 16.20/16.42  thf(t22_tops_2, conjecture,
% 16.20/16.42    (![A:$i]:
% 16.20/16.42     ( ( l1_pre_topc @ A ) =>
% 16.20/16.42       ( ![B:$i]:
% 16.20/16.42         ( ( m1_subset_1 @
% 16.20/16.42             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 16.20/16.42           ( ![C:$i]:
% 16.20/16.42             ( ( m1_subset_1 @
% 16.20/16.42                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 16.20/16.42               ( ( v1_tops_2 @ B @ A ) =>
% 16.20/16.42                 ( v1_tops_2 @
% 16.20/16.42                   ( k7_subset_1 @
% 16.20/16.42                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 16.20/16.42                   A ) ) ) ) ) ) ))).
% 16.20/16.42  thf(zf_stmt_0, negated_conjecture,
% 16.20/16.42    (~( ![A:$i]:
% 16.20/16.42        ( ( l1_pre_topc @ A ) =>
% 16.20/16.42          ( ![B:$i]:
% 16.20/16.42            ( ( m1_subset_1 @
% 16.20/16.42                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 16.20/16.42              ( ![C:$i]:
% 16.20/16.42                ( ( m1_subset_1 @
% 16.20/16.42                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 16.20/16.42                  ( ( v1_tops_2 @ B @ A ) =>
% 16.20/16.42                    ( v1_tops_2 @
% 16.20/16.42                      ( k7_subset_1 @
% 16.20/16.42                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 16.20/16.42                      A ) ) ) ) ) ) ) )),
% 16.20/16.42    inference('cnf.neg', [status(esa)], [t22_tops_2])).
% 16.20/16.42  thf('0', plain,
% 16.20/16.42      (~ (v1_tops_2 @ 
% 16.20/16.42          (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 16.20/16.42          sk_A)),
% 16.20/16.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.20/16.42  thf('1', plain,
% 16.20/16.42      ((m1_subset_1 @ sk_B @ 
% 16.20/16.42        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 16.20/16.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.20/16.42  thf(redefinition_k7_subset_1, axiom,
% 16.20/16.42    (![A:$i,B:$i,C:$i]:
% 16.20/16.42     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 16.20/16.42       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 16.20/16.42  thf('2', plain,
% 16.20/16.42      (![X41 : $i, X42 : $i, X43 : $i]:
% 16.20/16.42         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 16.20/16.42          | ((k7_subset_1 @ X42 @ X41 @ X43) = (k4_xboole_0 @ X41 @ X43)))),
% 16.20/16.42      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 16.20/16.42  thf('3', plain,
% 16.20/16.42      (![X0 : $i]:
% 16.20/16.42         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 16.20/16.42           = (k4_xboole_0 @ sk_B @ X0))),
% 16.20/16.42      inference('sup-', [status(thm)], ['1', '2'])).
% 16.20/16.42  thf('4', plain, (~ (v1_tops_2 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 16.20/16.42      inference('demod', [status(thm)], ['0', '3'])).
% 16.20/16.42  thf('5', plain,
% 16.20/16.42      ((m1_subset_1 @ sk_B @ 
% 16.20/16.42        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 16.20/16.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.20/16.42  thf('6', plain,
% 16.20/16.42      ((m1_subset_1 @ sk_B @ 
% 16.20/16.42        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 16.20/16.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.20/16.42  thf(t3_subset, axiom,
% 16.20/16.42    (![A:$i,B:$i]:
% 16.20/16.42     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 16.20/16.42  thf('7', plain,
% 16.20/16.42      (![X46 : $i, X47 : $i]:
% 16.20/16.42         ((r1_tarski @ X46 @ X47) | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47)))),
% 16.20/16.42      inference('cnf', [status(esa)], [t3_subset])).
% 16.20/16.42  thf('8', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.20/16.42      inference('sup-', [status(thm)], ['6', '7'])).
% 16.20/16.42  thf(d10_xboole_0, axiom,
% 16.20/16.42    (![A:$i,B:$i]:
% 16.20/16.42     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 16.20/16.42  thf('9', plain,
% 16.20/16.42      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 16.20/16.42      inference('cnf', [status(esa)], [d10_xboole_0])).
% 16.20/16.42  thf('10', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 16.20/16.42      inference('simplify', [status(thm)], ['9'])).
% 16.20/16.42  thf(t108_xboole_1, axiom,
% 16.20/16.42    (![A:$i,B:$i,C:$i]:
% 16.20/16.42     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 16.20/16.42  thf('11', plain,
% 16.20/16.42      (![X5 : $i, X6 : $i, X7 : $i]:
% 16.20/16.42         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ (k3_xboole_0 @ X5 @ X7) @ X6))),
% 16.20/16.42      inference('cnf', [status(esa)], [t108_xboole_1])).
% 16.20/16.42  thf(t12_setfam_1, axiom,
% 16.20/16.42    (![A:$i,B:$i]:
% 16.20/16.42     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 16.20/16.42  thf('12', plain,
% 16.20/16.42      (![X44 : $i, X45 : $i]:
% 16.20/16.42         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 16.20/16.42      inference('cnf', [status(esa)], [t12_setfam_1])).
% 16.20/16.42  thf('13', plain,
% 16.20/16.42      (![X5 : $i, X6 : $i, X7 : $i]:
% 16.20/16.42         (~ (r1_tarski @ X5 @ X6)
% 16.20/16.42          | (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X5 @ X7)) @ X6))),
% 16.20/16.42      inference('demod', [status(thm)], ['11', '12'])).
% 16.20/16.42  thf('14', plain,
% 16.20/16.42      (![X0 : $i, X1 : $i]:
% 16.20/16.42         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 16.20/16.42      inference('sup-', [status(thm)], ['10', '13'])).
% 16.20/16.42  thf('15', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 16.20/16.42      inference('simplify', [status(thm)], ['9'])).
% 16.20/16.42  thf(t110_xboole_1, axiom,
% 16.20/16.42    (![A:$i,B:$i,C:$i]:
% 16.20/16.42     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 16.20/16.42       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 16.20/16.42  thf('16', plain,
% 16.20/16.42      (![X8 : $i, X9 : $i, X10 : $i]:
% 16.20/16.42         (~ (r1_tarski @ X8 @ X9)
% 16.20/16.42          | ~ (r1_tarski @ X10 @ X9)
% 16.20/16.42          | (r1_tarski @ (k5_xboole_0 @ X8 @ X10) @ X9))),
% 16.20/16.42      inference('cnf', [status(esa)], [t110_xboole_1])).
% 16.20/16.42  thf('17', plain,
% 16.20/16.42      (![X0 : $i, X1 : $i]:
% 16.20/16.42         ((r1_tarski @ (k5_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 16.20/16.42      inference('sup-', [status(thm)], ['15', '16'])).
% 16.20/16.42  thf('18', plain,
% 16.20/16.42      (![X0 : $i, X1 : $i]:
% 16.20/16.42         (r1_tarski @ 
% 16.20/16.42          (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ X0)),
% 16.20/16.42      inference('sup-', [status(thm)], ['14', '17'])).
% 16.20/16.42  thf(t100_xboole_1, axiom,
% 16.20/16.42    (![A:$i,B:$i]:
% 16.20/16.42     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 16.20/16.42  thf('19', plain,
% 16.20/16.42      (![X3 : $i, X4 : $i]:
% 16.20/16.42         ((k4_xboole_0 @ X3 @ X4)
% 16.20/16.42           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 16.20/16.42      inference('cnf', [status(esa)], [t100_xboole_1])).
% 16.20/16.42  thf('20', plain,
% 16.20/16.42      (![X44 : $i, X45 : $i]:
% 16.20/16.42         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 16.20/16.42      inference('cnf', [status(esa)], [t12_setfam_1])).
% 16.20/16.42  thf('21', plain,
% 16.20/16.42      (![X3 : $i, X4 : $i]:
% 16.20/16.42         ((k4_xboole_0 @ X3 @ X4)
% 16.20/16.42           = (k5_xboole_0 @ X3 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4))))),
% 16.20/16.42      inference('demod', [status(thm)], ['19', '20'])).
% 16.20/16.42  thf('22', plain,
% 16.20/16.42      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 16.20/16.42      inference('demod', [status(thm)], ['18', '21'])).
% 16.20/16.42  thf(t1_xboole_1, axiom,
% 16.20/16.42    (![A:$i,B:$i,C:$i]:
% 16.20/16.42     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 16.20/16.42       ( r1_tarski @ A @ C ) ))).
% 16.20/16.42  thf('23', plain,
% 16.20/16.42      (![X11 : $i, X12 : $i, X13 : $i]:
% 16.20/16.42         (~ (r1_tarski @ X11 @ X12)
% 16.20/16.42          | ~ (r1_tarski @ X12 @ X13)
% 16.20/16.42          | (r1_tarski @ X11 @ X13))),
% 16.20/16.42      inference('cnf', [status(esa)], [t1_xboole_1])).
% 16.20/16.42  thf('24', plain,
% 16.20/16.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.20/16.42         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 16.20/16.42      inference('sup-', [status(thm)], ['22', '23'])).
% 16.20/16.42  thf('25', plain,
% 16.20/16.42      (![X0 : $i]:
% 16.20/16.42         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ 
% 16.20/16.42          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.20/16.42      inference('sup-', [status(thm)], ['8', '24'])).
% 16.20/16.42  thf('26', plain,
% 16.20/16.42      (![X46 : $i, X48 : $i]:
% 16.20/16.42         ((m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X48)) | ~ (r1_tarski @ X46 @ X48))),
% 16.20/16.42      inference('cnf', [status(esa)], [t3_subset])).
% 16.20/16.42  thf('27', plain,
% 16.20/16.42      (![X0 : $i]:
% 16.20/16.42         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 16.20/16.42          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 16.20/16.42      inference('sup-', [status(thm)], ['25', '26'])).
% 16.20/16.42  thf(t18_tops_2, axiom,
% 16.20/16.42    (![A:$i]:
% 16.20/16.43     ( ( l1_pre_topc @ A ) =>
% 16.20/16.43       ( ![B:$i]:
% 16.20/16.43         ( ( m1_subset_1 @
% 16.20/16.43             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 16.20/16.43           ( ![C:$i]:
% 16.20/16.43             ( ( m1_subset_1 @
% 16.20/16.43                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 16.20/16.43               ( ( ( r1_tarski @ B @ C ) & ( v1_tops_2 @ C @ A ) ) =>
% 16.20/16.43                 ( v1_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 16.20/16.43  thf('28', plain,
% 16.20/16.43      (![X49 : $i, X50 : $i, X51 : $i]:
% 16.20/16.43         (~ (m1_subset_1 @ X49 @ 
% 16.20/16.43             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50))))
% 16.20/16.43          | (v1_tops_2 @ X49 @ X50)
% 16.20/16.43          | ~ (r1_tarski @ X49 @ X51)
% 16.20/16.43          | ~ (v1_tops_2 @ X51 @ X50)
% 16.20/16.43          | ~ (m1_subset_1 @ X51 @ 
% 16.20/16.43               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50))))
% 16.20/16.43          | ~ (l1_pre_topc @ X50))),
% 16.20/16.43      inference('cnf', [status(esa)], [t18_tops_2])).
% 16.20/16.43  thf('29', plain,
% 16.20/16.43      (![X0 : $i, X1 : $i]:
% 16.20/16.43         (~ (l1_pre_topc @ sk_A)
% 16.20/16.43          | ~ (m1_subset_1 @ X1 @ 
% 16.20/16.43               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 16.20/16.43          | ~ (v1_tops_2 @ X1 @ sk_A)
% 16.20/16.43          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1)
% 16.20/16.43          | (v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 16.20/16.43      inference('sup-', [status(thm)], ['27', '28'])).
% 16.20/16.43  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 16.20/16.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.20/16.43  thf('31', plain,
% 16.20/16.43      (![X0 : $i, X1 : $i]:
% 16.20/16.43         (~ (m1_subset_1 @ X1 @ 
% 16.20/16.43             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 16.20/16.43          | ~ (v1_tops_2 @ X1 @ sk_A)
% 16.20/16.43          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1)
% 16.20/16.43          | (v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 16.20/16.43      inference('demod', [status(thm)], ['29', '30'])).
% 16.20/16.43  thf('32', plain,
% 16.20/16.43      (![X0 : $i]:
% 16.20/16.43         ((v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)
% 16.20/16.43          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 16.20/16.43          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 16.20/16.43      inference('sup-', [status(thm)], ['5', '31'])).
% 16.20/16.43  thf('33', plain,
% 16.20/16.43      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 16.20/16.43      inference('demod', [status(thm)], ['18', '21'])).
% 16.20/16.43  thf('34', plain, ((v1_tops_2 @ sk_B @ sk_A)),
% 16.20/16.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.20/16.43  thf('35', plain,
% 16.20/16.43      (![X0 : $i]: (v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 16.20/16.43      inference('demod', [status(thm)], ['32', '33', '34'])).
% 16.20/16.43  thf('36', plain, ($false), inference('demod', [status(thm)], ['4', '35'])).
% 16.20/16.43  
% 16.20/16.43  % SZS output end Refutation
% 16.20/16.43  
% 16.28/16.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hm0LnJouu8

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:21 EST 2020

% Result     : Theorem 15.10s
% Output     : Refutation 15.10s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 113 expanded)
%              Number of leaves         :   28 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :  494 (1041 expanded)
%              Number of equality atoms :   15 (  35 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k7_subset_1 @ X39 @ X38 @ X40 )
        = ( k4_xboole_0 @ X38 @ X40 ) ) ) ),
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

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X11 @ X11 @ X12 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k3_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X7 ) ) @ X6 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t110_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k5_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X11 @ X11 @ X12 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

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
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( r1_tarski @ C @ B )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) ) )
      | ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) ) )
      | ~ ( r1_tarski @ X49 @ X47 )
      | ~ ( l1_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_tops_2])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('28',plain,(
    ! [X43: $i] :
      ( ( l1_struct_0 @ X43 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

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

thf('32',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) ) )
      | ( v1_tops_2 @ X44 @ X45 )
      | ~ ( r1_tarski @ X44 @ X46 )
      | ~ ( v1_tops_2 @ X46 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t18_tops_2])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('38',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['4','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hm0LnJouu8
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:06:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 15.10/15.29  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 15.10/15.29  % Solved by: fo/fo7.sh
% 15.10/15.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.10/15.29  % done 1779 iterations in 14.843s
% 15.10/15.29  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 15.10/15.29  % SZS output start Refutation
% 15.10/15.29  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 15.10/15.29  thf(sk_A_type, type, sk_A: $i).
% 15.10/15.29  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 15.10/15.29  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 15.10/15.29  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 15.10/15.29  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 15.10/15.29  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 15.10/15.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 15.10/15.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 15.10/15.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 15.10/15.29  thf(sk_C_type, type, sk_C: $i).
% 15.10/15.29  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 15.10/15.29  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 15.10/15.29  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 15.10/15.29  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 15.10/15.29  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 15.10/15.29  thf(sk_B_type, type, sk_B: $i).
% 15.10/15.29  thf(t22_tops_2, conjecture,
% 15.10/15.29    (![A:$i]:
% 15.10/15.29     ( ( l1_pre_topc @ A ) =>
% 15.10/15.29       ( ![B:$i]:
% 15.10/15.29         ( ( m1_subset_1 @
% 15.10/15.29             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 15.10/15.29           ( ![C:$i]:
% 15.10/15.29             ( ( m1_subset_1 @
% 15.10/15.29                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 15.10/15.29               ( ( v1_tops_2 @ B @ A ) =>
% 15.10/15.29                 ( v1_tops_2 @
% 15.10/15.29                   ( k7_subset_1 @
% 15.10/15.29                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 15.10/15.29                   A ) ) ) ) ) ) ))).
% 15.10/15.29  thf(zf_stmt_0, negated_conjecture,
% 15.10/15.29    (~( ![A:$i]:
% 15.10/15.29        ( ( l1_pre_topc @ A ) =>
% 15.10/15.29          ( ![B:$i]:
% 15.10/15.29            ( ( m1_subset_1 @
% 15.10/15.29                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 15.10/15.29              ( ![C:$i]:
% 15.10/15.29                ( ( m1_subset_1 @
% 15.10/15.29                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 15.10/15.29                  ( ( v1_tops_2 @ B @ A ) =>
% 15.10/15.29                    ( v1_tops_2 @
% 15.10/15.29                      ( k7_subset_1 @
% 15.10/15.29                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 15.10/15.29                      A ) ) ) ) ) ) ) )),
% 15.10/15.29    inference('cnf.neg', [status(esa)], [t22_tops_2])).
% 15.10/15.29  thf('0', plain,
% 15.10/15.29      (~ (v1_tops_2 @ 
% 15.10/15.29          (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 15.10/15.29          sk_A)),
% 15.10/15.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.10/15.29  thf('1', plain,
% 15.10/15.29      ((m1_subset_1 @ sk_B @ 
% 15.10/15.29        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 15.10/15.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.10/15.29  thf(redefinition_k7_subset_1, axiom,
% 15.10/15.29    (![A:$i,B:$i,C:$i]:
% 15.10/15.29     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 15.10/15.29       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 15.10/15.29  thf('2', plain,
% 15.10/15.29      (![X38 : $i, X39 : $i, X40 : $i]:
% 15.10/15.29         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 15.10/15.29          | ((k7_subset_1 @ X39 @ X38 @ X40) = (k4_xboole_0 @ X38 @ X40)))),
% 15.10/15.29      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 15.10/15.29  thf('3', plain,
% 15.10/15.29      (![X0 : $i]:
% 15.10/15.29         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 15.10/15.29           = (k4_xboole_0 @ sk_B @ X0))),
% 15.10/15.29      inference('sup-', [status(thm)], ['1', '2'])).
% 15.10/15.29  thf('4', plain, (~ (v1_tops_2 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 15.10/15.29      inference('demod', [status(thm)], ['0', '3'])).
% 15.10/15.29  thf('5', plain,
% 15.10/15.29      ((m1_subset_1 @ sk_B @ 
% 15.10/15.29        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 15.10/15.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.10/15.29  thf(t70_enumset1, axiom,
% 15.10/15.29    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 15.10/15.29  thf('6', plain,
% 15.10/15.29      (![X11 : $i, X12 : $i]:
% 15.10/15.29         ((k1_enumset1 @ X11 @ X11 @ X12) = (k2_tarski @ X11 @ X12))),
% 15.10/15.29      inference('cnf', [status(esa)], [t70_enumset1])).
% 15.10/15.29  thf(d10_xboole_0, axiom,
% 15.10/15.29    (![A:$i,B:$i]:
% 15.10/15.29     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 15.10/15.29  thf('7', plain,
% 15.10/15.29      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 15.10/15.29      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.10/15.29  thf('8', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 15.10/15.29      inference('simplify', [status(thm)], ['7'])).
% 15.10/15.29  thf(t108_xboole_1, axiom,
% 15.10/15.29    (![A:$i,B:$i,C:$i]:
% 15.10/15.29     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 15.10/15.29  thf('9', plain,
% 15.10/15.29      (![X5 : $i, X6 : $i, X7 : $i]:
% 15.10/15.29         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ (k3_xboole_0 @ X5 @ X7) @ X6))),
% 15.10/15.29      inference('cnf', [status(esa)], [t108_xboole_1])).
% 15.10/15.29  thf(t12_setfam_1, axiom,
% 15.10/15.29    (![A:$i,B:$i]:
% 15.10/15.29     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 15.10/15.29  thf('10', plain,
% 15.10/15.29      (![X41 : $i, X42 : $i]:
% 15.10/15.29         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 15.10/15.29      inference('cnf', [status(esa)], [t12_setfam_1])).
% 15.10/15.29  thf('11', plain,
% 15.10/15.29      (![X5 : $i, X6 : $i, X7 : $i]:
% 15.10/15.29         (~ (r1_tarski @ X5 @ X6)
% 15.10/15.29          | (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X5 @ X7)) @ X6))),
% 15.10/15.29      inference('demod', [status(thm)], ['9', '10'])).
% 15.10/15.29  thf('12', plain,
% 15.10/15.29      (![X0 : $i, X1 : $i]:
% 15.10/15.29         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 15.10/15.29      inference('sup-', [status(thm)], ['8', '11'])).
% 15.10/15.29  thf('13', plain,
% 15.10/15.29      (![X0 : $i, X1 : $i]:
% 15.10/15.29         (r1_tarski @ (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0)) @ X1)),
% 15.10/15.29      inference('sup+', [status(thm)], ['6', '12'])).
% 15.10/15.29  thf('14', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 15.10/15.29      inference('simplify', [status(thm)], ['7'])).
% 15.10/15.29  thf(t110_xboole_1, axiom,
% 15.10/15.29    (![A:$i,B:$i,C:$i]:
% 15.10/15.29     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 15.10/15.29       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 15.10/15.29  thf('15', plain,
% 15.10/15.29      (![X8 : $i, X9 : $i, X10 : $i]:
% 15.10/15.29         (~ (r1_tarski @ X8 @ X9)
% 15.10/15.29          | ~ (r1_tarski @ X10 @ X9)
% 15.10/15.29          | (r1_tarski @ (k5_xboole_0 @ X8 @ X10) @ X9))),
% 15.10/15.29      inference('cnf', [status(esa)], [t110_xboole_1])).
% 15.10/15.29  thf('16', plain,
% 15.10/15.29      (![X0 : $i, X1 : $i]:
% 15.10/15.29         ((r1_tarski @ (k5_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 15.10/15.29      inference('sup-', [status(thm)], ['14', '15'])).
% 15.10/15.29  thf('17', plain,
% 15.10/15.29      (![X0 : $i, X1 : $i]:
% 15.10/15.29         (r1_tarski @ 
% 15.10/15.29          (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k1_enumset1 @ X0 @ X0 @ X1))) @ 
% 15.10/15.29          X0)),
% 15.10/15.29      inference('sup-', [status(thm)], ['13', '16'])).
% 15.10/15.29  thf('18', plain,
% 15.10/15.29      (![X11 : $i, X12 : $i]:
% 15.10/15.29         ((k1_enumset1 @ X11 @ X11 @ X12) = (k2_tarski @ X11 @ X12))),
% 15.10/15.29      inference('cnf', [status(esa)], [t70_enumset1])).
% 15.10/15.29  thf(t100_xboole_1, axiom,
% 15.10/15.29    (![A:$i,B:$i]:
% 15.10/15.29     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 15.10/15.29  thf('19', plain,
% 15.10/15.29      (![X3 : $i, X4 : $i]:
% 15.10/15.29         ((k4_xboole_0 @ X3 @ X4)
% 15.10/15.29           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 15.10/15.29      inference('cnf', [status(esa)], [t100_xboole_1])).
% 15.10/15.29  thf('20', plain,
% 15.10/15.29      (![X41 : $i, X42 : $i]:
% 15.10/15.29         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 15.10/15.29      inference('cnf', [status(esa)], [t12_setfam_1])).
% 15.10/15.29  thf('21', plain,
% 15.10/15.29      (![X3 : $i, X4 : $i]:
% 15.10/15.29         ((k4_xboole_0 @ X3 @ X4)
% 15.10/15.29           = (k5_xboole_0 @ X3 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4))))),
% 15.10/15.29      inference('demod', [status(thm)], ['19', '20'])).
% 15.10/15.29  thf('22', plain,
% 15.10/15.29      (![X0 : $i, X1 : $i]:
% 15.10/15.29         ((k4_xboole_0 @ X1 @ X0)
% 15.10/15.29           = (k5_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0))))),
% 15.10/15.29      inference('sup+', [status(thm)], ['18', '21'])).
% 15.10/15.29  thf('23', plain,
% 15.10/15.29      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 15.10/15.29      inference('demod', [status(thm)], ['17', '22'])).
% 15.10/15.29  thf('24', plain,
% 15.10/15.29      ((m1_subset_1 @ sk_B @ 
% 15.10/15.29        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 15.10/15.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.10/15.29  thf(t3_tops_2, axiom,
% 15.10/15.29    (![A:$i]:
% 15.10/15.29     ( ( l1_struct_0 @ A ) =>
% 15.10/15.29       ( ![B:$i]:
% 15.10/15.29         ( ( m1_subset_1 @
% 15.10/15.29             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 15.10/15.29           ( ![C:$i]:
% 15.10/15.29             ( ( r1_tarski @ C @ B ) =>
% 15.10/15.29               ( m1_subset_1 @
% 15.10/15.29                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 15.10/15.29  thf('25', plain,
% 15.10/15.29      (![X47 : $i, X48 : $i, X49 : $i]:
% 15.10/15.29         (~ (m1_subset_1 @ X47 @ 
% 15.10/15.29             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48))))
% 15.10/15.29          | (m1_subset_1 @ X49 @ 
% 15.10/15.29             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48))))
% 15.10/15.29          | ~ (r1_tarski @ X49 @ X47)
% 15.10/15.29          | ~ (l1_struct_0 @ X48))),
% 15.10/15.29      inference('cnf', [status(esa)], [t3_tops_2])).
% 15.10/15.29  thf('26', plain,
% 15.10/15.29      (![X0 : $i]:
% 15.10/15.29         (~ (l1_struct_0 @ sk_A)
% 15.10/15.29          | ~ (r1_tarski @ X0 @ sk_B)
% 15.10/15.29          | (m1_subset_1 @ X0 @ 
% 15.10/15.29             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.10/15.29      inference('sup-', [status(thm)], ['24', '25'])).
% 15.10/15.29  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 15.10/15.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.10/15.29  thf(dt_l1_pre_topc, axiom,
% 15.10/15.29    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 15.10/15.29  thf('28', plain,
% 15.10/15.29      (![X43 : $i]: ((l1_struct_0 @ X43) | ~ (l1_pre_topc @ X43))),
% 15.10/15.29      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 15.10/15.29  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 15.10/15.29      inference('sup-', [status(thm)], ['27', '28'])).
% 15.10/15.29  thf('30', plain,
% 15.10/15.29      (![X0 : $i]:
% 15.10/15.29         (~ (r1_tarski @ X0 @ sk_B)
% 15.10/15.29          | (m1_subset_1 @ X0 @ 
% 15.10/15.29             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 15.10/15.29      inference('demod', [status(thm)], ['26', '29'])).
% 15.10/15.29  thf('31', plain,
% 15.10/15.29      (![X0 : $i]:
% 15.10/15.29         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 15.10/15.29          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 15.10/15.29      inference('sup-', [status(thm)], ['23', '30'])).
% 15.10/15.29  thf(t18_tops_2, axiom,
% 15.10/15.29    (![A:$i]:
% 15.10/15.29     ( ( l1_pre_topc @ A ) =>
% 15.10/15.29       ( ![B:$i]:
% 15.10/15.29         ( ( m1_subset_1 @
% 15.10/15.29             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 15.10/15.29           ( ![C:$i]:
% 15.10/15.29             ( ( m1_subset_1 @
% 15.10/15.29                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 15.10/15.29               ( ( ( r1_tarski @ B @ C ) & ( v1_tops_2 @ C @ A ) ) =>
% 15.10/15.29                 ( v1_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 15.10/15.29  thf('32', plain,
% 15.10/15.29      (![X44 : $i, X45 : $i, X46 : $i]:
% 15.10/15.29         (~ (m1_subset_1 @ X44 @ 
% 15.10/15.29             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45))))
% 15.10/15.29          | (v1_tops_2 @ X44 @ X45)
% 15.10/15.29          | ~ (r1_tarski @ X44 @ X46)
% 15.10/15.29          | ~ (v1_tops_2 @ X46 @ X45)
% 15.10/15.29          | ~ (m1_subset_1 @ X46 @ 
% 15.10/15.29               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45))))
% 15.10/15.29          | ~ (l1_pre_topc @ X45))),
% 15.10/15.29      inference('cnf', [status(esa)], [t18_tops_2])).
% 15.10/15.29  thf('33', plain,
% 15.10/15.29      (![X0 : $i, X1 : $i]:
% 15.10/15.29         (~ (l1_pre_topc @ sk_A)
% 15.10/15.29          | ~ (m1_subset_1 @ X1 @ 
% 15.10/15.29               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 15.10/15.29          | ~ (v1_tops_2 @ X1 @ sk_A)
% 15.10/15.29          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1)
% 15.10/15.29          | (v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 15.10/15.29      inference('sup-', [status(thm)], ['31', '32'])).
% 15.10/15.29  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 15.10/15.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.10/15.29  thf('35', plain,
% 15.10/15.29      (![X0 : $i, X1 : $i]:
% 15.10/15.29         (~ (m1_subset_1 @ X1 @ 
% 15.10/15.29             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 15.10/15.29          | ~ (v1_tops_2 @ X1 @ sk_A)
% 15.10/15.29          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1)
% 15.10/15.29          | (v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 15.10/15.29      inference('demod', [status(thm)], ['33', '34'])).
% 15.10/15.29  thf('36', plain,
% 15.10/15.29      (![X0 : $i]:
% 15.10/15.29         ((v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)
% 15.10/15.29          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 15.10/15.29          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 15.10/15.29      inference('sup-', [status(thm)], ['5', '35'])).
% 15.10/15.29  thf('37', plain,
% 15.10/15.29      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 15.10/15.29      inference('demod', [status(thm)], ['17', '22'])).
% 15.10/15.29  thf('38', plain, ((v1_tops_2 @ sk_B @ sk_A)),
% 15.10/15.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.10/15.29  thf('39', plain,
% 15.10/15.29      (![X0 : $i]: (v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 15.10/15.29      inference('demod', [status(thm)], ['36', '37', '38'])).
% 15.10/15.29  thf('40', plain, ($false), inference('demod', [status(thm)], ['4', '39'])).
% 15.10/15.29  
% 15.10/15.29  % SZS output end Refutation
% 15.10/15.29  
% 15.10/15.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

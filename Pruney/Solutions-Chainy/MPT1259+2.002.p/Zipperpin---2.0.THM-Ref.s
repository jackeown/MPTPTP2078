%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4P1mUQM940

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:19 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 132 expanded)
%              Number of leaves         :   27 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :  618 (1449 expanded)
%              Number of equality atoms :   35 (  68 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(t75_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
            = ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
              = ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( l1_pre_topc @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X41 @ X42 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( l1_pre_topc @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X41 @ X42 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( ( k2_tops_1 @ X44 @ X43 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X44 ) @ ( k2_pre_topc @ X44 @ X43 ) @ ( k1_tops_1 @ X44 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l79_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ ( k2_tops_1 @ A @ B ) )
            = ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( ( k2_pre_topc @ X46 @ ( k2_tops_1 @ X46 @ X45 ) )
        = ( k2_tops_1 @ X46 @ X45 ) )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[l79_tops_1])).

thf('15',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l80_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
            = k1_xboole_0 ) ) ) )).

thf('20',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( ( k1_tops_1 @ X48 @ ( k2_tops_1 @ X48 @ ( k2_tops_1 @ X48 @ X47 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v2_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[l80_tops_1])).

thf('21',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k7_subset_1 @ X32 @ X31 @ X33 )
        = ( k4_xboole_0 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 )
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('28',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('37',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X30 @ ( k3_subset_1 @ X30 @ X29 ) )
        = X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('40',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['33'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('43',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','46'])).

thf('48',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','18','24','27','47'])).

thf('49',plain,(
    ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
 != ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4P1mUQM940
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:31:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.02/1.21  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.02/1.21  % Solved by: fo/fo7.sh
% 1.02/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.02/1.21  % done 3184 iterations in 0.756s
% 1.02/1.21  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.02/1.21  % SZS output start Refutation
% 1.02/1.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.02/1.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.02/1.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.02/1.21  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.02/1.21  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.02/1.21  thf(sk_A_type, type, sk_A: $i).
% 1.02/1.21  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.02/1.21  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.02/1.21  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.02/1.21  thf(sk_B_type, type, sk_B: $i).
% 1.02/1.21  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.02/1.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.02/1.21  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.02/1.21  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.02/1.21  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.02/1.21  thf(t75_tops_1, conjecture,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.21           ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 1.02/1.21             ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.02/1.21  thf(zf_stmt_0, negated_conjecture,
% 1.02/1.21    (~( ![A:$i]:
% 1.02/1.21        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.02/1.21          ( ![B:$i]:
% 1.02/1.21            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.21              ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 1.02/1.21                ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 1.02/1.21    inference('cnf.neg', [status(esa)], [t75_tops_1])).
% 1.02/1.21  thf('0', plain,
% 1.02/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf(dt_k2_tops_1, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( ( l1_pre_topc @ A ) & 
% 1.02/1.21         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.02/1.21       ( m1_subset_1 @
% 1.02/1.21         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.02/1.21  thf('1', plain,
% 1.02/1.21      (![X41 : $i, X42 : $i]:
% 1.02/1.21         (~ (l1_pre_topc @ X41)
% 1.02/1.21          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 1.02/1.21          | (m1_subset_1 @ (k2_tops_1 @ X41 @ X42) @ 
% 1.02/1.21             (k1_zfmisc_1 @ (u1_struct_0 @ X41))))),
% 1.02/1.21      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.02/1.21  thf('2', plain,
% 1.02/1.21      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.02/1.21         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.02/1.21        | ~ (l1_pre_topc @ sk_A))),
% 1.02/1.21      inference('sup-', [status(thm)], ['0', '1'])).
% 1.02/1.21  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('4', plain,
% 1.02/1.21      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.02/1.21        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('demod', [status(thm)], ['2', '3'])).
% 1.02/1.21  thf('5', plain,
% 1.02/1.21      (![X41 : $i, X42 : $i]:
% 1.02/1.21         (~ (l1_pre_topc @ X41)
% 1.02/1.21          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 1.02/1.21          | (m1_subset_1 @ (k2_tops_1 @ X41 @ X42) @ 
% 1.02/1.21             (k1_zfmisc_1 @ (u1_struct_0 @ X41))))),
% 1.02/1.21      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.02/1.21  thf('6', plain,
% 1.02/1.21      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.02/1.21         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.02/1.21        | ~ (l1_pre_topc @ sk_A))),
% 1.02/1.21      inference('sup-', [status(thm)], ['4', '5'])).
% 1.02/1.21  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('8', plain,
% 1.02/1.21      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.02/1.21        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('demod', [status(thm)], ['6', '7'])).
% 1.02/1.21  thf(l78_tops_1, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( l1_pre_topc @ A ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.21           ( ( k2_tops_1 @ A @ B ) =
% 1.02/1.21             ( k7_subset_1 @
% 1.02/1.21               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.02/1.21               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.02/1.21  thf('9', plain,
% 1.02/1.21      (![X43 : $i, X44 : $i]:
% 1.02/1.21         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 1.02/1.21          | ((k2_tops_1 @ X44 @ X43)
% 1.02/1.21              = (k7_subset_1 @ (u1_struct_0 @ X44) @ 
% 1.02/1.21                 (k2_pre_topc @ X44 @ X43) @ (k1_tops_1 @ X44 @ X43)))
% 1.02/1.21          | ~ (l1_pre_topc @ X44))),
% 1.02/1.21      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.02/1.21  thf('10', plain,
% 1.02/1.21      ((~ (l1_pre_topc @ sk_A)
% 1.02/1.21        | ((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.02/1.21            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21               (k2_pre_topc @ sk_A @ 
% 1.02/1.21                (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 1.02/1.21               (k1_tops_1 @ sk_A @ 
% 1.02/1.21                (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['8', '9'])).
% 1.02/1.21  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('12', plain,
% 1.02/1.21      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.02/1.21         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21            (k2_pre_topc @ sk_A @ 
% 1.02/1.21             (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 1.02/1.21            (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))))),
% 1.02/1.21      inference('demod', [status(thm)], ['10', '11'])).
% 1.02/1.21  thf('13', plain,
% 1.02/1.21      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.02/1.21        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('demod', [status(thm)], ['2', '3'])).
% 1.02/1.21  thf(l79_tops_1, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.21           ( ( k2_pre_topc @ A @ ( k2_tops_1 @ A @ B ) ) =
% 1.02/1.21             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 1.02/1.21  thf('14', plain,
% 1.02/1.21      (![X45 : $i, X46 : $i]:
% 1.02/1.21         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 1.02/1.21          | ((k2_pre_topc @ X46 @ (k2_tops_1 @ X46 @ X45))
% 1.02/1.21              = (k2_tops_1 @ X46 @ X45))
% 1.02/1.21          | ~ (l1_pre_topc @ X46)
% 1.02/1.21          | ~ (v2_pre_topc @ X46))),
% 1.02/1.21      inference('cnf', [status(esa)], [l79_tops_1])).
% 1.02/1.21  thf('15', plain,
% 1.02/1.21      ((~ (v2_pre_topc @ sk_A)
% 1.02/1.21        | ~ (l1_pre_topc @ sk_A)
% 1.02/1.21        | ((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.02/1.21            = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['13', '14'])).
% 1.02/1.21  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('18', plain,
% 1.02/1.21      (((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.02/1.21         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.02/1.21      inference('demod', [status(thm)], ['15', '16', '17'])).
% 1.02/1.21  thf('19', plain,
% 1.02/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf(l80_tops_1, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.21           ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 1.02/1.21             ( k1_xboole_0 ) ) ) ) ))).
% 1.02/1.21  thf('20', plain,
% 1.02/1.21      (![X47 : $i, X48 : $i]:
% 1.02/1.21         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 1.02/1.21          | ((k1_tops_1 @ X48 @ (k2_tops_1 @ X48 @ (k2_tops_1 @ X48 @ X47)))
% 1.02/1.21              = (k1_xboole_0))
% 1.02/1.21          | ~ (l1_pre_topc @ X48)
% 1.02/1.21          | ~ (v2_pre_topc @ X48))),
% 1.02/1.21      inference('cnf', [status(esa)], [l80_tops_1])).
% 1.02/1.21  thf('21', plain,
% 1.02/1.21      ((~ (v2_pre_topc @ sk_A)
% 1.02/1.21        | ~ (l1_pre_topc @ sk_A)
% 1.02/1.21        | ((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.02/1.21            = (k1_xboole_0)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['19', '20'])).
% 1.02/1.21  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('24', plain,
% 1.02/1.21      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.02/1.21         = (k1_xboole_0))),
% 1.02/1.21      inference('demod', [status(thm)], ['21', '22', '23'])).
% 1.02/1.21  thf('25', plain,
% 1.02/1.21      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.02/1.21        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('demod', [status(thm)], ['6', '7'])).
% 1.02/1.21  thf(redefinition_k7_subset_1, axiom,
% 1.02/1.21    (![A:$i,B:$i,C:$i]:
% 1.02/1.21     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.02/1.21       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.02/1.21  thf('26', plain,
% 1.02/1.21      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.02/1.21         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 1.02/1.21          | ((k7_subset_1 @ X32 @ X31 @ X33) = (k4_xboole_0 @ X31 @ X33)))),
% 1.02/1.21      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.02/1.21  thf('27', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21           (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0)
% 1.02/1.21           = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['25', '26'])).
% 1.02/1.21  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.02/1.21  thf('28', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 1.02/1.21      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.02/1.21  thf(t3_subset, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.02/1.21  thf('29', plain,
% 1.02/1.21      (![X34 : $i, X36 : $i]:
% 1.02/1.21         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 1.02/1.21      inference('cnf', [status(esa)], [t3_subset])).
% 1.02/1.21  thf('30', plain,
% 1.02/1.21      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['28', '29'])).
% 1.02/1.21  thf(d5_subset_1, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.02/1.21       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.02/1.21  thf('31', plain,
% 1.02/1.21      (![X27 : $i, X28 : $i]:
% 1.02/1.21         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 1.02/1.21          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 1.02/1.21      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.02/1.21  thf('32', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['30', '31'])).
% 1.02/1.21  thf(d10_xboole_0, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.02/1.21  thf('33', plain,
% 1.02/1.21      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 1.02/1.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.02/1.21  thf('34', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.02/1.21      inference('simplify', [status(thm)], ['33'])).
% 1.02/1.21  thf('35', plain,
% 1.02/1.21      (![X34 : $i, X36 : $i]:
% 1.02/1.21         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 1.02/1.21      inference('cnf', [status(esa)], [t3_subset])).
% 1.02/1.21  thf('36', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['34', '35'])).
% 1.02/1.21  thf(involutiveness_k3_subset_1, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.02/1.21       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.02/1.21  thf('37', plain,
% 1.02/1.21      (![X29 : $i, X30 : $i]:
% 1.02/1.21         (((k3_subset_1 @ X30 @ (k3_subset_1 @ X30 @ X29)) = (X29))
% 1.02/1.21          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30)))),
% 1.02/1.21      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.02/1.21  thf('38', plain,
% 1.02/1.21      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['36', '37'])).
% 1.02/1.21  thf('39', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['34', '35'])).
% 1.02/1.21  thf('40', plain,
% 1.02/1.21      (![X27 : $i, X28 : $i]:
% 1.02/1.21         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 1.02/1.21          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 1.02/1.21      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.02/1.21  thf('41', plain,
% 1.02/1.21      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['39', '40'])).
% 1.02/1.21  thf('42', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.02/1.21      inference('simplify', [status(thm)], ['33'])).
% 1.02/1.21  thf(l32_xboole_1, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.02/1.21  thf('43', plain,
% 1.02/1.21      (![X5 : $i, X7 : $i]:
% 1.02/1.21         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.02/1.21      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.02/1.21  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['42', '43'])).
% 1.02/1.21  thf('45', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.02/1.21      inference('sup+', [status(thm)], ['41', '44'])).
% 1.02/1.21  thf('46', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 1.02/1.21      inference('demod', [status(thm)], ['38', '45'])).
% 1.02/1.21  thf('47', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.02/1.21      inference('demod', [status(thm)], ['32', '46'])).
% 1.02/1.21  thf('48', plain,
% 1.02/1.21      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.02/1.21         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.02/1.21      inference('demod', [status(thm)], ['12', '18', '24', '27', '47'])).
% 1.02/1.21  thf('49', plain,
% 1.02/1.21      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.02/1.21         != (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('50', plain, ($false),
% 1.02/1.21      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 1.02/1.21  
% 1.02/1.21  % SZS output end Refutation
% 1.02/1.21  
% 1.02/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JvLCDI50HX

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:24 EST 2020

% Result     : Theorem 4.55s
% Output     : Refutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :   70 (  93 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  549 ( 926 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(t24_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( v2_tops_2 @ B @ A )
               => ( v2_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( v2_tops_2 @ B @ A )
                 => ( v2_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_tops_2])).

thf('0',plain,(
    ~ ( v2_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k9_subset_1 @ X22 @ X20 @ X21 )
        = ( k3_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tops_2 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X15 @ X14 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k4_subset_1 @ X18 @ X17 @ X19 )
        = ( k2_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    = ( k2_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t29_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k2_xboole_0 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    = ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k2_xboole_0 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('33',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf(t19_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( r1_tarski @ B @ C )
                  & ( v2_tops_2 @ C @ A ) )
               => ( v2_tops_2 @ B @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
      | ( v2_tops_2 @ X26 @ X27 )
      | ~ ( r1_tarski @ X26 @ X28 )
      | ~ ( v2_tops_2 @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t19_tops_2])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v2_tops_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v2_tops_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_tops_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ~ ( v2_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','39'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('41',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('42',plain,(
    v2_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( v2_tops_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['4','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JvLCDI50HX
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:26:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.55/4.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.55/4.78  % Solved by: fo/fo7.sh
% 4.55/4.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.55/4.78  % done 5465 iterations in 4.324s
% 4.55/4.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.55/4.78  % SZS output start Refutation
% 4.55/4.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.55/4.78  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.55/4.78  thf(sk_B_type, type, sk_B: $i).
% 4.55/4.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.55/4.78  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 4.55/4.78  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.55/4.78  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 4.55/4.78  thf(sk_C_type, type, sk_C: $i).
% 4.55/4.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.55/4.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.55/4.78  thf(sk_A_type, type, sk_A: $i).
% 4.55/4.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.55/4.78  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 4.55/4.78  thf(t24_tops_2, conjecture,
% 4.55/4.78    (![A:$i]:
% 4.55/4.78     ( ( l1_pre_topc @ A ) =>
% 4.55/4.78       ( ![B:$i]:
% 4.55/4.78         ( ( m1_subset_1 @
% 4.55/4.78             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.55/4.78           ( ![C:$i]:
% 4.55/4.78             ( ( m1_subset_1 @
% 4.55/4.78                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.55/4.78               ( ( v2_tops_2 @ B @ A ) =>
% 4.55/4.78                 ( v2_tops_2 @
% 4.55/4.78                   ( k9_subset_1 @
% 4.55/4.78                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 4.55/4.78                   A ) ) ) ) ) ) ))).
% 4.55/4.78  thf(zf_stmt_0, negated_conjecture,
% 4.55/4.78    (~( ![A:$i]:
% 4.55/4.78        ( ( l1_pre_topc @ A ) =>
% 4.55/4.78          ( ![B:$i]:
% 4.55/4.78            ( ( m1_subset_1 @
% 4.55/4.78                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.55/4.78              ( ![C:$i]:
% 4.55/4.78                ( ( m1_subset_1 @
% 4.55/4.78                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.55/4.78                  ( ( v2_tops_2 @ B @ A ) =>
% 4.55/4.78                    ( v2_tops_2 @
% 4.55/4.78                      ( k9_subset_1 @
% 4.55/4.78                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 4.55/4.78                      A ) ) ) ) ) ) ) )),
% 4.55/4.78    inference('cnf.neg', [status(esa)], [t24_tops_2])).
% 4.55/4.78  thf('0', plain,
% 4.55/4.78      (~ (v2_tops_2 @ 
% 4.55/4.78          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 4.55/4.78          sk_A)),
% 4.55/4.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.78  thf('1', plain,
% 4.55/4.78      ((m1_subset_1 @ sk_C @ 
% 4.55/4.78        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.55/4.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.78  thf(redefinition_k9_subset_1, axiom,
% 4.55/4.78    (![A:$i,B:$i,C:$i]:
% 4.55/4.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 4.55/4.78       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 4.55/4.78  thf('2', plain,
% 4.55/4.78      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.55/4.78         (((k9_subset_1 @ X22 @ X20 @ X21) = (k3_xboole_0 @ X20 @ X21))
% 4.55/4.78          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 4.55/4.78      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 4.55/4.78  thf('3', plain,
% 4.55/4.78      (![X0 : $i]:
% 4.55/4.78         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C)
% 4.55/4.78           = (k3_xboole_0 @ X0 @ sk_C))),
% 4.55/4.78      inference('sup-', [status(thm)], ['1', '2'])).
% 4.55/4.78  thf('4', plain, (~ (v2_tops_2 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 4.55/4.78      inference('demod', [status(thm)], ['0', '3'])).
% 4.55/4.78  thf('5', plain,
% 4.55/4.78      ((m1_subset_1 @ sk_B @ 
% 4.55/4.78        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.55/4.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.78  thf(d10_xboole_0, axiom,
% 4.55/4.78    (![A:$i,B:$i]:
% 4.55/4.78     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.55/4.78  thf('6', plain,
% 4.55/4.78      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 4.55/4.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.55/4.78  thf('7', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 4.55/4.78      inference('simplify', [status(thm)], ['6'])).
% 4.55/4.78  thf(t3_subset, axiom,
% 4.55/4.78    (![A:$i,B:$i]:
% 4.55/4.78     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.55/4.78  thf('8', plain,
% 4.55/4.78      (![X23 : $i, X25 : $i]:
% 4.55/4.78         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 4.55/4.78      inference('cnf', [status(esa)], [t3_subset])).
% 4.55/4.78  thf('9', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.55/4.78      inference('sup-', [status(thm)], ['7', '8'])).
% 4.55/4.78  thf('10', plain,
% 4.55/4.78      ((m1_subset_1 @ sk_B @ 
% 4.55/4.78        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.55/4.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.78  thf(dt_k4_subset_1, axiom,
% 4.55/4.78    (![A:$i,B:$i,C:$i]:
% 4.55/4.78     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 4.55/4.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 4.55/4.78       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 4.55/4.78  thf('11', plain,
% 4.55/4.78      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.55/4.78         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 4.55/4.78          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15))
% 4.55/4.78          | (m1_subset_1 @ (k4_subset_1 @ X15 @ X14 @ X16) @ 
% 4.55/4.78             (k1_zfmisc_1 @ X15)))),
% 4.55/4.78      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 4.55/4.78  thf('12', plain,
% 4.55/4.78      (![X0 : $i]:
% 4.55/4.78         ((m1_subset_1 @ 
% 4.55/4.78           (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0) @ 
% 4.55/4.78           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 4.55/4.78          | ~ (m1_subset_1 @ X0 @ 
% 4.55/4.78               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.55/4.78      inference('sup-', [status(thm)], ['10', '11'])).
% 4.55/4.78  thf('13', plain,
% 4.55/4.78      ((m1_subset_1 @ 
% 4.55/4.78        (k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ 
% 4.55/4.78         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 4.55/4.78        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.55/4.78      inference('sup-', [status(thm)], ['9', '12'])).
% 4.55/4.78  thf('14', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.55/4.78      inference('sup-', [status(thm)], ['7', '8'])).
% 4.55/4.78  thf('15', plain,
% 4.55/4.78      ((m1_subset_1 @ sk_B @ 
% 4.55/4.78        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.55/4.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.78  thf(redefinition_k4_subset_1, axiom,
% 4.55/4.78    (![A:$i,B:$i,C:$i]:
% 4.55/4.78     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 4.55/4.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 4.55/4.78       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 4.55/4.78  thf('16', plain,
% 4.55/4.78      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.55/4.78         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 4.55/4.78          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18))
% 4.55/4.78          | ((k4_subset_1 @ X18 @ X17 @ X19) = (k2_xboole_0 @ X17 @ X19)))),
% 4.55/4.78      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 4.55/4.78  thf('17', plain,
% 4.55/4.78      (![X0 : $i]:
% 4.55/4.78         (((k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 4.55/4.78            = (k2_xboole_0 @ sk_B @ X0))
% 4.55/4.78          | ~ (m1_subset_1 @ X0 @ 
% 4.55/4.78               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.55/4.78      inference('sup-', [status(thm)], ['15', '16'])).
% 4.55/4.78  thf('18', plain,
% 4.55/4.78      (((k4_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ 
% 4.55/4.78         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.55/4.78         = (k2_xboole_0 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.55/4.78      inference('sup-', [status(thm)], ['14', '17'])).
% 4.55/4.78  thf('19', plain,
% 4.55/4.78      ((m1_subset_1 @ 
% 4.55/4.78        (k2_xboole_0 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 4.55/4.78        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.55/4.78      inference('demod', [status(thm)], ['13', '18'])).
% 4.55/4.78  thf('20', plain,
% 4.55/4.78      (![X23 : $i, X24 : $i]:
% 4.55/4.78         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 4.55/4.78      inference('cnf', [status(esa)], [t3_subset])).
% 4.55/4.78  thf('21', plain,
% 4.55/4.78      ((r1_tarski @ 
% 4.55/4.78        (k2_xboole_0 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))) @ 
% 4.55/4.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.55/4.78      inference('sup-', [status(thm)], ['19', '20'])).
% 4.55/4.78  thf(commutativity_k2_xboole_0, axiom,
% 4.55/4.78    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 4.55/4.78  thf('22', plain,
% 4.55/4.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.55/4.78      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.55/4.78  thf('23', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 4.55/4.78      inference('simplify', [status(thm)], ['6'])).
% 4.55/4.78  thf(t28_xboole_1, axiom,
% 4.55/4.78    (![A:$i,B:$i]:
% 4.55/4.78     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.55/4.78  thf('24', plain,
% 4.55/4.78      (![X7 : $i, X8 : $i]:
% 4.55/4.78         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 4.55/4.78      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.55/4.78  thf('25', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 4.55/4.78      inference('sup-', [status(thm)], ['23', '24'])).
% 4.55/4.78  thf(t29_xboole_1, axiom,
% 4.55/4.78    (![A:$i,B:$i,C:$i]:
% 4.55/4.78     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 4.55/4.78  thf('26', plain,
% 4.55/4.78      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.55/4.78         (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ (k2_xboole_0 @ X9 @ X11))),
% 4.55/4.78      inference('cnf', [status(esa)], [t29_xboole_1])).
% 4.55/4.78  thf('27', plain,
% 4.55/4.78      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 4.55/4.78      inference('sup+', [status(thm)], ['25', '26'])).
% 4.55/4.78  thf('28', plain,
% 4.55/4.78      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 4.55/4.78      inference('sup+', [status(thm)], ['22', '27'])).
% 4.55/4.78  thf('29', plain,
% 4.55/4.78      (![X2 : $i, X4 : $i]:
% 4.55/4.78         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 4.55/4.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.55/4.78  thf('30', plain,
% 4.55/4.78      (![X0 : $i, X1 : $i]:
% 4.55/4.78         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 4.55/4.78          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 4.55/4.78      inference('sup-', [status(thm)], ['28', '29'])).
% 4.55/4.78  thf('31', plain,
% 4.55/4.78      (((k2_xboole_0 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.55/4.78         = (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.55/4.78      inference('sup-', [status(thm)], ['21', '30'])).
% 4.55/4.78  thf('32', plain,
% 4.55/4.78      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.55/4.78         (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ (k2_xboole_0 @ X9 @ X11))),
% 4.55/4.78      inference('cnf', [status(esa)], [t29_xboole_1])).
% 4.55/4.78  thf('33', plain,
% 4.55/4.78      (![X23 : $i, X25 : $i]:
% 4.55/4.78         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 4.55/4.78      inference('cnf', [status(esa)], [t3_subset])).
% 4.55/4.78  thf('34', plain,
% 4.55/4.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.55/4.78         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X2) @ 
% 4.55/4.78          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.55/4.78      inference('sup-', [status(thm)], ['32', '33'])).
% 4.55/4.78  thf('35', plain,
% 4.55/4.78      (![X0 : $i]:
% 4.55/4.78         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 4.55/4.78          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.55/4.78      inference('sup+', [status(thm)], ['31', '34'])).
% 4.55/4.78  thf(t19_tops_2, axiom,
% 4.55/4.78    (![A:$i]:
% 4.55/4.78     ( ( l1_pre_topc @ A ) =>
% 4.55/4.78       ( ![B:$i]:
% 4.55/4.78         ( ( m1_subset_1 @
% 4.55/4.78             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.55/4.78           ( ![C:$i]:
% 4.55/4.78             ( ( m1_subset_1 @
% 4.55/4.78                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.55/4.78               ( ( ( r1_tarski @ B @ C ) & ( v2_tops_2 @ C @ A ) ) =>
% 4.55/4.78                 ( v2_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 4.55/4.78  thf('36', plain,
% 4.55/4.78      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.55/4.78         (~ (m1_subset_1 @ X26 @ 
% 4.55/4.78             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))
% 4.55/4.78          | (v2_tops_2 @ X26 @ X27)
% 4.55/4.78          | ~ (r1_tarski @ X26 @ X28)
% 4.55/4.78          | ~ (v2_tops_2 @ X28 @ X27)
% 4.55/4.78          | ~ (m1_subset_1 @ X28 @ 
% 4.55/4.78               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))
% 4.55/4.78          | ~ (l1_pre_topc @ X27))),
% 4.55/4.78      inference('cnf', [status(esa)], [t19_tops_2])).
% 4.55/4.78  thf('37', plain,
% 4.55/4.78      (![X0 : $i, X1 : $i]:
% 4.55/4.78         (~ (l1_pre_topc @ sk_A)
% 4.55/4.78          | ~ (m1_subset_1 @ X1 @ 
% 4.55/4.78               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 4.55/4.78          | ~ (v2_tops_2 @ X1 @ sk_A)
% 4.55/4.78          | ~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ X1)
% 4.55/4.78          | (v2_tops_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))),
% 4.55/4.78      inference('sup-', [status(thm)], ['35', '36'])).
% 4.55/4.78  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 4.55/4.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.78  thf('39', plain,
% 4.55/4.78      (![X0 : $i, X1 : $i]:
% 4.55/4.78         (~ (m1_subset_1 @ X1 @ 
% 4.55/4.78             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 4.55/4.78          | ~ (v2_tops_2 @ X1 @ sk_A)
% 4.55/4.78          | ~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ X1)
% 4.55/4.78          | (v2_tops_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))),
% 4.55/4.78      inference('demod', [status(thm)], ['37', '38'])).
% 4.55/4.78  thf('40', plain,
% 4.55/4.78      (![X0 : $i]:
% 4.55/4.78         ((v2_tops_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 4.55/4.78          | ~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)
% 4.55/4.78          | ~ (v2_tops_2 @ sk_B @ sk_A))),
% 4.55/4.78      inference('sup-', [status(thm)], ['5', '39'])).
% 4.55/4.78  thf(t17_xboole_1, axiom,
% 4.55/4.78    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 4.55/4.78  thf('41', plain,
% 4.55/4.78      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 4.55/4.78      inference('cnf', [status(esa)], [t17_xboole_1])).
% 4.55/4.78  thf('42', plain, ((v2_tops_2 @ sk_B @ sk_A)),
% 4.55/4.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.78  thf('43', plain,
% 4.55/4.78      (![X0 : $i]: (v2_tops_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)),
% 4.55/4.78      inference('demod', [status(thm)], ['40', '41', '42'])).
% 4.55/4.78  thf('44', plain, ($false), inference('demod', [status(thm)], ['4', '43'])).
% 4.55/4.78  
% 4.55/4.78  % SZS output end Refutation
% 4.55/4.78  
% 4.55/4.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

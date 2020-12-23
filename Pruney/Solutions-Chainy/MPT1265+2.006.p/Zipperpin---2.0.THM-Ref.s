%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lQK7wFxqB8

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:11 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 154 expanded)
%              Number of leaves         :   23 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  590 (2257 expanded)
%              Number of equality atoms :   30 (  56 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t82_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v1_tops_1 @ B @ A )
                  & ( v1_tops_1 @ C @ A )
                  & ( v3_pre_topc @ C @ A ) )
               => ( v1_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v1_tops_1 @ B @ A )
                    & ( v1_tops_1 @ C @ A )
                    & ( v3_pre_topc @ C @ A ) )
                 => ( v1_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t82_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t81_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( v3_pre_topc @ C @ A )
                 => ( ( k2_pre_topc @ A @ C )
                    = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X25 @ X24 )
      | ( ( k2_pre_topc @ X24 @ X25 )
        = ( k2_pre_topc @ X24 @ ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ X25 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v1_tops_1 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t81_tops_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tops_1 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X13 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','9'])).

thf('11',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_C )
      = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v1_tops_1 @ X21 @ X22 )
      | ( ( k2_pre_topc @ X22 @ X21 )
        = ( k2_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_tops_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X8 @ X10 @ X9 )
        = ( k9_subset_1 @ X8 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X13 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['11','12','18','27'])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k2_pre_topc @ X22 @ X21 )
       != ( k2_struct_0 @ X22 ) )
      | ( v1_tops_1 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_tops_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) )
       != ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) )
       != ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( v1_tops_1 @ ( k3_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','42'])).

thf('44',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('45',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( v1_tops_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v1_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('48',plain,(
    ~ ( v1_tops_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['45','48'])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lQK7wFxqB8
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/0.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.95  % Solved by: fo/fo7.sh
% 0.76/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.95  % done 555 iterations in 0.496s
% 0.76/0.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.95  % SZS output start Refutation
% 0.76/0.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.95  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.76/0.95  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.76/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.95  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.76/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.95  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.95  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.76/0.95  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.95  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.76/0.95  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.76/0.95  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.76/0.95  thf(t82_tops_1, conjecture,
% 0.76/0.95    (![A:$i]:
% 0.76/0.95     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.95       ( ![B:$i]:
% 0.76/0.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.95           ( ![C:$i]:
% 0.76/0.95             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.95               ( ( ( v1_tops_1 @ B @ A ) & ( v1_tops_1 @ C @ A ) & 
% 0.76/0.95                   ( v3_pre_topc @ C @ A ) ) =>
% 0.76/0.95                 ( v1_tops_1 @
% 0.76/0.95                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.76/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.95    (~( ![A:$i]:
% 0.76/0.95        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.95          ( ![B:$i]:
% 0.76/0.95            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.95              ( ![C:$i]:
% 0.76/0.95                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.95                  ( ( ( v1_tops_1 @ B @ A ) & ( v1_tops_1 @ C @ A ) & 
% 0.76/0.95                      ( v3_pre_topc @ C @ A ) ) =>
% 0.76/0.95                    ( v1_tops_1 @
% 0.76/0.95                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.76/0.95    inference('cnf.neg', [status(esa)], [t82_tops_1])).
% 0.76/0.95  thf('0', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('1', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(t81_tops_1, axiom,
% 0.76/0.95    (![A:$i]:
% 0.76/0.95     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.95       ( ![B:$i]:
% 0.76/0.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.95           ( ( v1_tops_1 @ B @ A ) =>
% 0.76/0.95             ( ![C:$i]:
% 0.76/0.95               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.95                 ( ( v3_pre_topc @ C @ A ) =>
% 0.76/0.95                   ( ( k2_pre_topc @ A @ C ) =
% 0.76/0.95                     ( k2_pre_topc @
% 0.76/0.95                       A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.95  thf('2', plain,
% 0.76/0.95      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.76/0.95          | ~ (v3_pre_topc @ X25 @ X24)
% 0.76/0.95          | ((k2_pre_topc @ X24 @ X25)
% 0.76/0.95              = (k2_pre_topc @ X24 @ 
% 0.76/0.95                 (k9_subset_1 @ (u1_struct_0 @ X24) @ X25 @ X23)))
% 0.76/0.95          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.76/0.95          | ~ (v1_tops_1 @ X23 @ X24)
% 0.76/0.95          | ~ (l1_pre_topc @ X24)
% 0.76/0.95          | ~ (v2_pre_topc @ X24))),
% 0.76/0.95      inference('cnf', [status(esa)], [t81_tops_1])).
% 0.76/0.95  thf('3', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (~ (v2_pre_topc @ sk_A)
% 0.76/0.95          | ~ (l1_pre_topc @ sk_A)
% 0.76/0.95          | ~ (v1_tops_1 @ sk_B @ sk_A)
% 0.76/0.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.95          | ((k2_pre_topc @ sk_A @ X0)
% 0.76/0.95              = (k2_pre_topc @ sk_A @ 
% 0.76/0.95                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)))
% 0.76/0.95          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/0.95  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('6', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('7', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(redefinition_k9_subset_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.95       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.76/0.95  thf('8', plain,
% 0.76/0.95      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.76/0.95         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 0.76/0.95          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.76/0.95      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.76/0.95  thf('9', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.76/0.95           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.76/0.95      inference('sup-', [status(thm)], ['7', '8'])).
% 0.76/0.95  thf('10', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.95          | ((k2_pre_topc @ sk_A @ X0)
% 0.76/0.95              = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)))
% 0.76/0.95          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 0.76/0.95      inference('demod', [status(thm)], ['3', '4', '5', '6', '9'])).
% 0.76/0.95  thf('11', plain,
% 0.76/0.95      ((~ (v3_pre_topc @ sk_C @ sk_A)
% 0.76/0.95        | ((k2_pre_topc @ sk_A @ sk_C)
% 0.76/0.95            = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['0', '10'])).
% 0.76/0.95  thf('12', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('13', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(d3_tops_1, axiom,
% 0.76/0.95    (![A:$i]:
% 0.76/0.95     ( ( l1_pre_topc @ A ) =>
% 0.76/0.95       ( ![B:$i]:
% 0.76/0.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.95           ( ( v1_tops_1 @ B @ A ) <=>
% 0.76/0.95             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.76/0.95  thf('14', plain,
% 0.76/0.95      (![X21 : $i, X22 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.76/0.95          | ~ (v1_tops_1 @ X21 @ X22)
% 0.76/0.95          | ((k2_pre_topc @ X22 @ X21) = (k2_struct_0 @ X22))
% 0.76/0.95          | ~ (l1_pre_topc @ X22))),
% 0.76/0.95      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.76/0.95  thf('15', plain,
% 0.76/0.95      ((~ (l1_pre_topc @ sk_A)
% 0.76/0.95        | ((k2_pre_topc @ sk_A @ sk_C) = (k2_struct_0 @ sk_A))
% 0.76/0.95        | ~ (v1_tops_1 @ sk_C @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['13', '14'])).
% 0.76/0.95  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('17', plain, ((v1_tops_1 @ sk_C @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('18', plain, (((k2_pre_topc @ sk_A @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.76/0.95      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.76/0.95  thf('19', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(commutativity_k9_subset_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.95       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.76/0.95  thf('20', plain,
% 0.76/0.95      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.76/0.95         (((k9_subset_1 @ X8 @ X10 @ X9) = (k9_subset_1 @ X8 @ X9 @ X10))
% 0.76/0.95          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.76/0.95      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.76/0.95  thf('21', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.76/0.95           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.76/0.95      inference('sup-', [status(thm)], ['19', '20'])).
% 0.76/0.95  thf('22', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.76/0.95           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.76/0.95      inference('sup-', [status(thm)], ['7', '8'])).
% 0.76/0.95  thf('23', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((k3_xboole_0 @ X0 @ sk_B)
% 0.76/0.95           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.76/0.95      inference('demod', [status(thm)], ['21', '22'])).
% 0.76/0.95  thf('24', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('25', plain,
% 0.76/0.95      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.76/0.95         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 0.76/0.95          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.76/0.95      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.76/0.95  thf('26', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.76/0.95           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.76/0.95      inference('sup-', [status(thm)], ['24', '25'])).
% 0.76/0.95  thf('27', plain,
% 0.76/0.95      (((k3_xboole_0 @ sk_C @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.76/0.95      inference('sup+', [status(thm)], ['23', '26'])).
% 0.76/0.95  thf('28', plain,
% 0.76/0.95      (((k2_struct_0 @ sk_A)
% 0.76/0.95         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.76/0.95      inference('demod', [status(thm)], ['11', '12', '18', '27'])).
% 0.76/0.95  thf('29', plain,
% 0.76/0.95      (((k3_xboole_0 @ sk_C @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.76/0.95      inference('sup+', [status(thm)], ['23', '26'])).
% 0.76/0.95  thf('30', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(t3_subset, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.95  thf('31', plain,
% 0.76/0.95      (![X16 : $i, X17 : $i]:
% 0.76/0.95         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.76/0.95      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.95  thf('32', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['30', '31'])).
% 0.76/0.95  thf(t17_xboole_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.76/0.95  thf('33', plain,
% 0.76/0.95      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.76/0.95      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.76/0.95  thf(t1_xboole_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.76/0.95       ( r1_tarski @ A @ C ) ))).
% 0.76/0.95  thf('34', plain,
% 0.76/0.95      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.76/0.95         (~ (r1_tarski @ X5 @ X6)
% 0.76/0.95          | ~ (r1_tarski @ X6 @ X7)
% 0.76/0.95          | (r1_tarski @ X5 @ X7))),
% 0.76/0.95      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.76/0.95  thf('35', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.95         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.76/0.95      inference('sup-', [status(thm)], ['33', '34'])).
% 0.76/0.95  thf('36', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ (u1_struct_0 @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['32', '35'])).
% 0.76/0.95  thf('37', plain,
% 0.76/0.95      (![X16 : $i, X18 : $i]:
% 0.76/0.95         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 0.76/0.95      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.95  thf('38', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (m1_subset_1 @ (k3_xboole_0 @ sk_C @ X0) @ 
% 0.76/0.95          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['36', '37'])).
% 0.76/0.95  thf('39', plain,
% 0.76/0.95      (![X21 : $i, X22 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.76/0.95          | ((k2_pre_topc @ X22 @ X21) != (k2_struct_0 @ X22))
% 0.76/0.95          | (v1_tops_1 @ X21 @ X22)
% 0.76/0.95          | ~ (l1_pre_topc @ X22))),
% 0.76/0.95      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.76/0.95  thf('40', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (~ (l1_pre_topc @ sk_A)
% 0.76/0.95          | (v1_tops_1 @ (k3_xboole_0 @ sk_C @ X0) @ sk_A)
% 0.76/0.95          | ((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0))
% 0.76/0.95              != (k2_struct_0 @ sk_A)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['38', '39'])).
% 0.76/0.95  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('42', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((v1_tops_1 @ (k3_xboole_0 @ sk_C @ X0) @ sk_A)
% 0.76/0.95          | ((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0))
% 0.76/0.95              != (k2_struct_0 @ sk_A)))),
% 0.76/0.95      inference('demod', [status(thm)], ['40', '41'])).
% 0.76/0.95  thf('43', plain,
% 0.76/0.95      ((((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.76/0.95          != (k2_struct_0 @ sk_A))
% 0.76/0.95        | (v1_tops_1 @ (k3_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['29', '42'])).
% 0.76/0.95  thf('44', plain,
% 0.76/0.95      (((k3_xboole_0 @ sk_C @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.76/0.95      inference('sup+', [status(thm)], ['23', '26'])).
% 0.76/0.95  thf('45', plain,
% 0.76/0.95      ((((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.76/0.95          != (k2_struct_0 @ sk_A))
% 0.76/0.95        | (v1_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.76/0.95      inference('demod', [status(thm)], ['43', '44'])).
% 0.76/0.95  thf('46', plain,
% 0.76/0.95      (~ (v1_tops_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('47', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.76/0.95           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.76/0.95      inference('sup-', [status(thm)], ['24', '25'])).
% 0.76/0.95  thf('48', plain, (~ (v1_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.76/0.95      inference('demod', [status(thm)], ['46', '47'])).
% 0.76/0.95  thf('49', plain,
% 0.76/0.95      (((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.76/0.95         != (k2_struct_0 @ sk_A))),
% 0.76/0.95      inference('clc', [status(thm)], ['45', '48'])).
% 0.76/0.95  thf('50', plain, ($false),
% 0.76/0.95      inference('simplify_reflect-', [status(thm)], ['28', '49'])).
% 0.76/0.95  
% 0.76/0.95  % SZS output end Refutation
% 0.76/0.95  
% 0.76/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

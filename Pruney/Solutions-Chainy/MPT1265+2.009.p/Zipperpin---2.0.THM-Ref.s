%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6icuGII2Nt

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:11 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 154 expanded)
%              Number of leaves         :   23 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  590 (2257 expanded)
%              Number of equality atoms :   30 (  56 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X24 @ X23 )
      | ( ( k2_pre_topc @ X23 @ X24 )
        = ( k2_pre_topc @ X23 @ ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X24 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v1_tops_1 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v1_tops_1 @ X20 @ X21 )
      | ( ( k2_pre_topc @ X21 @ X20 )
        = ( k2_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X5 @ X7 @ X6 )
        = ( k9_subset_1 @ X5 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('34',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
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
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k2_pre_topc @ X21 @ X20 )
       != ( k2_struct_0 @ X21 ) )
      | ( v1_tops_1 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6icuGII2Nt
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.94  % Solved by: fo/fo7.sh
% 0.75/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.94  % done 481 iterations in 0.491s
% 0.75/0.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.94  % SZS output start Refutation
% 0.75/0.94  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.75/0.94  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.75/0.94  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.94  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.75/0.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.94  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.75/0.94  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.75/0.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.94  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.75/0.94  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.75/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.94  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.75/0.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.94  thf(t82_tops_1, conjecture,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/0.94       ( ![B:$i]:
% 0.75/0.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.94           ( ![C:$i]:
% 0.75/0.94             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.94               ( ( ( v1_tops_1 @ B @ A ) & ( v1_tops_1 @ C @ A ) & 
% 0.75/0.94                   ( v3_pre_topc @ C @ A ) ) =>
% 0.75/0.94                 ( v1_tops_1 @
% 0.75/0.94                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.75/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.94    (~( ![A:$i]:
% 0.75/0.94        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/0.94          ( ![B:$i]:
% 0.75/0.94            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.94              ( ![C:$i]:
% 0.75/0.94                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.94                  ( ( ( v1_tops_1 @ B @ A ) & ( v1_tops_1 @ C @ A ) & 
% 0.75/0.94                      ( v3_pre_topc @ C @ A ) ) =>
% 0.75/0.94                    ( v1_tops_1 @
% 0.75/0.94                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.75/0.94    inference('cnf.neg', [status(esa)], [t82_tops_1])).
% 0.75/0.94  thf('0', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('1', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(t81_tops_1, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/0.94       ( ![B:$i]:
% 0.75/0.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.94           ( ( v1_tops_1 @ B @ A ) =>
% 0.75/0.94             ( ![C:$i]:
% 0.75/0.94               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.94                 ( ( v3_pre_topc @ C @ A ) =>
% 0.75/0.94                   ( ( k2_pre_topc @ A @ C ) =
% 0.75/0.94                     ( k2_pre_topc @
% 0.75/0.94                       A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ))).
% 0.75/0.94  thf('2', plain,
% 0.75/0.94      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.75/0.94          | ~ (v3_pre_topc @ X24 @ X23)
% 0.75/0.94          | ((k2_pre_topc @ X23 @ X24)
% 0.75/0.94              = (k2_pre_topc @ X23 @ 
% 0.75/0.94                 (k9_subset_1 @ (u1_struct_0 @ X23) @ X24 @ X22)))
% 0.75/0.94          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.75/0.94          | ~ (v1_tops_1 @ X22 @ X23)
% 0.75/0.94          | ~ (l1_pre_topc @ X23)
% 0.75/0.94          | ~ (v2_pre_topc @ X23))),
% 0.75/0.94      inference('cnf', [status(esa)], [t81_tops_1])).
% 0.75/0.94  thf('3', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (v2_pre_topc @ sk_A)
% 0.75/0.94          | ~ (l1_pre_topc @ sk_A)
% 0.75/0.94          | ~ (v1_tops_1 @ sk_B @ sk_A)
% 0.75/0.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/0.94          | ((k2_pre_topc @ sk_A @ X0)
% 0.75/0.94              = (k2_pre_topc @ sk_A @ 
% 0.75/0.94                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)))
% 0.75/0.94          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['1', '2'])).
% 0.75/0.94  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('6', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('7', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(redefinition_k9_subset_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.94       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.75/0.94  thf('8', plain,
% 0.75/0.94      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.75/0.94         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.75/0.94          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.75/0.94      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.75/0.94  thf('9', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.75/0.94           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.75/0.94      inference('sup-', [status(thm)], ['7', '8'])).
% 0.75/0.94  thf('10', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/0.94          | ((k2_pre_topc @ sk_A @ X0)
% 0.75/0.94              = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)))
% 0.75/0.94          | ~ (v3_pre_topc @ X0 @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['3', '4', '5', '6', '9'])).
% 0.75/0.94  thf('11', plain,
% 0.75/0.94      ((~ (v3_pre_topc @ sk_C @ sk_A)
% 0.75/0.94        | ((k2_pre_topc @ sk_A @ sk_C)
% 0.75/0.94            = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['0', '10'])).
% 0.75/0.94  thf('12', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('13', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(d3_tops_1, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( l1_pre_topc @ A ) =>
% 0.75/0.94       ( ![B:$i]:
% 0.75/0.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.94           ( ( v1_tops_1 @ B @ A ) <=>
% 0.75/0.94             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.75/0.94  thf('14', plain,
% 0.75/0.94      (![X20 : $i, X21 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.75/0.94          | ~ (v1_tops_1 @ X20 @ X21)
% 0.75/0.94          | ((k2_pre_topc @ X21 @ X20) = (k2_struct_0 @ X21))
% 0.75/0.94          | ~ (l1_pre_topc @ X21))),
% 0.75/0.94      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.75/0.94  thf('15', plain,
% 0.75/0.94      ((~ (l1_pre_topc @ sk_A)
% 0.75/0.94        | ((k2_pre_topc @ sk_A @ sk_C) = (k2_struct_0 @ sk_A))
% 0.75/0.94        | ~ (v1_tops_1 @ sk_C @ sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['13', '14'])).
% 0.75/0.94  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('17', plain, ((v1_tops_1 @ sk_C @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('18', plain, (((k2_pre_topc @ sk_A @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.75/0.94  thf('19', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(commutativity_k9_subset_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.94       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.75/0.94  thf('20', plain,
% 0.75/0.94      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.75/0.94         (((k9_subset_1 @ X5 @ X7 @ X6) = (k9_subset_1 @ X5 @ X6 @ X7))
% 0.75/0.94          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.75/0.94      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.75/0.94  thf('21', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.75/0.94           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['19', '20'])).
% 0.75/0.94  thf('22', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.75/0.94           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.75/0.94      inference('sup-', [status(thm)], ['7', '8'])).
% 0.75/0.94  thf('23', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ X0 @ sk_B)
% 0.75/0.94           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['21', '22'])).
% 0.75/0.94  thf('24', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('25', plain,
% 0.75/0.94      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.75/0.94         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.75/0.94          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.75/0.94      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.75/0.94  thf('26', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.75/0.94           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.75/0.94      inference('sup-', [status(thm)], ['24', '25'])).
% 0.75/0.94  thf('27', plain,
% 0.75/0.94      (((k3_xboole_0 @ sk_C @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.75/0.94      inference('sup+', [status(thm)], ['23', '26'])).
% 0.75/0.94  thf('28', plain,
% 0.75/0.94      (((k2_struct_0 @ sk_A)
% 0.75/0.94         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.75/0.94      inference('demod', [status(thm)], ['11', '12', '18', '27'])).
% 0.75/0.94  thf('29', plain,
% 0.75/0.94      (((k3_xboole_0 @ sk_C @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.75/0.94      inference('sup+', [status(thm)], ['23', '26'])).
% 0.75/0.94  thf('30', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(t3_subset, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.75/0.94  thf('31', plain,
% 0.75/0.94      (![X15 : $i, X16 : $i]:
% 0.75/0.94         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_subset])).
% 0.75/0.94  thf('32', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['30', '31'])).
% 0.75/0.94  thf(t17_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.75/0.94  thf('33', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.75/0.94      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.75/0.94  thf(t1_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.75/0.94       ( r1_tarski @ A @ C ) ))).
% 0.75/0.94  thf('34', plain,
% 0.75/0.94      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.75/0.94         (~ (r1_tarski @ X2 @ X3)
% 0.75/0.94          | ~ (r1_tarski @ X3 @ X4)
% 0.75/0.94          | (r1_tarski @ X2 @ X4))),
% 0.75/0.94      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.75/0.94  thf('35', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.75/0.94      inference('sup-', [status(thm)], ['33', '34'])).
% 0.75/0.94  thf('36', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ (u1_struct_0 @ sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['32', '35'])).
% 0.75/0.94  thf('37', plain,
% 0.75/0.94      (![X15 : $i, X17 : $i]:
% 0.75/0.94         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_subset])).
% 0.75/0.94  thf('38', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (m1_subset_1 @ (k3_xboole_0 @ sk_C @ X0) @ 
% 0.75/0.94          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['36', '37'])).
% 0.75/0.94  thf('39', plain,
% 0.75/0.94      (![X20 : $i, X21 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.75/0.94          | ((k2_pre_topc @ X21 @ X20) != (k2_struct_0 @ X21))
% 0.75/0.94          | (v1_tops_1 @ X20 @ X21)
% 0.75/0.94          | ~ (l1_pre_topc @ X21))),
% 0.75/0.94      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.75/0.94  thf('40', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (l1_pre_topc @ sk_A)
% 0.75/0.94          | (v1_tops_1 @ (k3_xboole_0 @ sk_C @ X0) @ sk_A)
% 0.75/0.94          | ((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0))
% 0.75/0.94              != (k2_struct_0 @ sk_A)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['38', '39'])).
% 0.75/0.94  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('42', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((v1_tops_1 @ (k3_xboole_0 @ sk_C @ X0) @ sk_A)
% 0.75/0.94          | ((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0))
% 0.75/0.94              != (k2_struct_0 @ sk_A)))),
% 0.75/0.94      inference('demod', [status(thm)], ['40', '41'])).
% 0.75/0.94  thf('43', plain,
% 0.75/0.94      ((((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.75/0.94          != (k2_struct_0 @ sk_A))
% 0.75/0.94        | (v1_tops_1 @ (k3_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['29', '42'])).
% 0.75/0.94  thf('44', plain,
% 0.75/0.94      (((k3_xboole_0 @ sk_C @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.75/0.94      inference('sup+', [status(thm)], ['23', '26'])).
% 0.75/0.94  thf('45', plain,
% 0.75/0.94      ((((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.75/0.94          != (k2_struct_0 @ sk_A))
% 0.75/0.94        | (v1_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['43', '44'])).
% 0.75/0.94  thf('46', plain,
% 0.75/0.94      (~ (v1_tops_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('47', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.75/0.94           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.75/0.94      inference('sup-', [status(thm)], ['24', '25'])).
% 0.75/0.94  thf('48', plain, (~ (v1_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.75/0.94      inference('demod', [status(thm)], ['46', '47'])).
% 0.75/0.94  thf('49', plain,
% 0.75/0.94      (((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.75/0.94         != (k2_struct_0 @ sk_A))),
% 0.75/0.94      inference('clc', [status(thm)], ['45', '48'])).
% 0.75/0.94  thf('50', plain, ($false),
% 0.75/0.94      inference('simplify_reflect-', [status(thm)], ['28', '49'])).
% 0.75/0.94  
% 0.75/0.94  % SZS output end Refutation
% 0.75/0.94  
% 0.75/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XESVlOVr1g

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:02 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   67 (  83 expanded)
%              Number of leaves         :   32 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :  414 ( 702 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X2 )
        = X1 )
      | ~ ( r1_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t29_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_yellow_6])).

thf('4',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
            <=> ~ ( r1_waybel_0 @ A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( l1_waybel_0 @ X20 @ X21 )
      | ( r1_waybel_0 @ X21 @ X20 @ ( k6_subset_1 @ ( u1_struct_0 @ X21 ) @ X22 ) )
      | ( r2_waybel_0 @ X21 @ X20 @ X22 )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t10_waybel_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( l1_waybel_0 @ X20 @ X21 )
      | ( r1_waybel_0 @ X21 @ X20 @ ( k4_xboole_0 @ ( u1_struct_0 @ X21 ) @ X22 ) )
      | ( r2_waybel_0 @ X21 @ X20 @ X22 )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['15','16'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('18',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( sk_B @ X4 ) @ X4 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(d12_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
            <=> ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                 => ? [E: $i] :
                      ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C )
                      & ( r1_orders_2 @ B @ D @ E )
                      & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X15 )
      | ~ ( r2_waybel_0 @ X15 @ X14 @ X18 )
      | ( r2_hidden @ ( k2_waybel_0 @ X15 @ X14 @ ( sk_E @ X19 @ X18 @ X14 @ X15 ) ) @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ X0 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ k1_xboole_0 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['26','27'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('29',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('30',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XESVlOVr1g
% 0.16/0.37  % Computer   : n013.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 15:28:40 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.36/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.52  % Solved by: fo/fo7.sh
% 0.36/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.52  % done 47 iterations in 0.039s
% 0.36/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.52  % SZS output start Refutation
% 0.36/0.52  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.36/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.52  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.36/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.52  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.36/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.52  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.36/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.52  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.36/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.52  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.36/0.52  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.36/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.52  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.36/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.52  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.36/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.52  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.52  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.36/0.52  thf('1', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.36/0.52      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.36/0.52  thf(t83_xboole_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.52  thf('2', plain,
% 0.36/0.52      (![X1 : $i, X2 : $i]:
% 0.36/0.52         (((k4_xboole_0 @ X1 @ X2) = (X1)) | ~ (r1_xboole_0 @ X1 @ X2))),
% 0.36/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.36/0.52  thf('3', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.52  thf(t29_yellow_6, conjecture,
% 0.36/0.52    (![A:$i]:
% 0.36/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.52       ( ![B:$i]:
% 0.36/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.36/0.52             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.36/0.52           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.36/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.52    (~( ![A:$i]:
% 0.36/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.52          ( ![B:$i]:
% 0.36/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.36/0.52                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.36/0.52              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.36/0.52    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.36/0.52  thf('4', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf(t10_waybel_0, axiom,
% 0.36/0.52    (![A:$i]:
% 0.36/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.52       ( ![B:$i]:
% 0.36/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.36/0.52           ( ![C:$i]:
% 0.36/0.52             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.36/0.52               ( ~( r1_waybel_0 @
% 0.36/0.52                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.36/0.52  thf('5', plain,
% 0.36/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.52         ((v2_struct_0 @ X20)
% 0.36/0.52          | ~ (l1_waybel_0 @ X20 @ X21)
% 0.36/0.52          | (r1_waybel_0 @ X21 @ X20 @ 
% 0.36/0.52             (k6_subset_1 @ (u1_struct_0 @ X21) @ X22))
% 0.36/0.52          | (r2_waybel_0 @ X21 @ X20 @ X22)
% 0.36/0.52          | ~ (l1_struct_0 @ X21)
% 0.36/0.52          | (v2_struct_0 @ X21))),
% 0.36/0.52      inference('cnf', [status(esa)], [t10_waybel_0])).
% 0.36/0.52  thf(redefinition_k6_subset_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.36/0.52  thf('6', plain,
% 0.36/0.52      (![X5 : $i, X6 : $i]: ((k6_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))),
% 0.36/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.36/0.52  thf('7', plain,
% 0.36/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.52         ((v2_struct_0 @ X20)
% 0.36/0.52          | ~ (l1_waybel_0 @ X20 @ X21)
% 0.36/0.52          | (r1_waybel_0 @ X21 @ X20 @ 
% 0.36/0.52             (k4_xboole_0 @ (u1_struct_0 @ X21) @ X22))
% 0.36/0.52          | (r2_waybel_0 @ X21 @ X20 @ X22)
% 0.36/0.52          | ~ (l1_struct_0 @ X21)
% 0.36/0.52          | (v2_struct_0 @ X21))),
% 0.36/0.52      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.52  thf('8', plain,
% 0.36/0.52      (![X0 : $i]:
% 0.36/0.52         ((v2_struct_0 @ sk_A)
% 0.36/0.52          | ~ (l1_struct_0 @ sk_A)
% 0.36/0.52          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.36/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.36/0.52             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.36/0.52          | (v2_struct_0 @ sk_B_1))),
% 0.36/0.52      inference('sup-', [status(thm)], ['4', '7'])).
% 0.36/0.52  thf('9', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('10', plain,
% 0.36/0.52      (![X0 : $i]:
% 0.36/0.52         ((v2_struct_0 @ sk_A)
% 0.36/0.52          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.36/0.52          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.36/0.52             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.36/0.52          | (v2_struct_0 @ sk_B_1))),
% 0.36/0.52      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.52  thf('11', plain,
% 0.36/0.52      (((r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.52        | (v2_struct_0 @ sk_B_1)
% 0.36/0.52        | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)
% 0.36/0.52        | (v2_struct_0 @ sk_A))),
% 0.36/0.52      inference('sup+', [status(thm)], ['3', '10'])).
% 0.36/0.52  thf('12', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('13', plain,
% 0.36/0.52      (((v2_struct_0 @ sk_A)
% 0.36/0.52        | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)
% 0.36/0.52        | (v2_struct_0 @ sk_B_1))),
% 0.36/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.52  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('15', plain,
% 0.36/0.52      (((v2_struct_0 @ sk_B_1) | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0))),
% 0.36/0.52      inference('clc', [status(thm)], ['13', '14'])).
% 0.36/0.52  thf('16', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('17', plain, ((r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)),
% 0.36/0.52      inference('clc', [status(thm)], ['15', '16'])).
% 0.36/0.52  thf(existence_m1_subset_1, axiom,
% 0.36/0.52    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.36/0.52  thf('18', plain, (![X4 : $i]: (m1_subset_1 @ (sk_B @ X4) @ X4)),
% 0.36/0.52      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.36/0.52  thf(d12_waybel_0, axiom,
% 0.36/0.52    (![A:$i]:
% 0.36/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.52       ( ![B:$i]:
% 0.36/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.36/0.52           ( ![C:$i]:
% 0.36/0.52             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.36/0.52               ( ![D:$i]:
% 0.36/0.52                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.36/0.52                   ( ?[E:$i]:
% 0.36/0.52                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.36/0.52                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.36/0.52                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.52  thf('19', plain,
% 0.36/0.52      (![X14 : $i, X15 : $i, X18 : $i, X19 : $i]:
% 0.36/0.52         ((v2_struct_0 @ X14)
% 0.36/0.52          | ~ (l1_waybel_0 @ X14 @ X15)
% 0.36/0.52          | ~ (r2_waybel_0 @ X15 @ X14 @ X18)
% 0.36/0.52          | (r2_hidden @ 
% 0.36/0.52             (k2_waybel_0 @ X15 @ X14 @ (sk_E @ X19 @ X18 @ X14 @ X15)) @ X18)
% 0.36/0.52          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X14))
% 0.36/0.52          | ~ (l1_struct_0 @ X15)
% 0.36/0.52          | (v2_struct_0 @ X15))),
% 0.36/0.52      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.36/0.52  thf('20', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.52         ((v2_struct_0 @ X1)
% 0.36/0.52          | ~ (l1_struct_0 @ X1)
% 0.36/0.52          | (r2_hidden @ 
% 0.36/0.52             (k2_waybel_0 @ X1 @ X0 @ 
% 0.36/0.52              (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1)) @ 
% 0.36/0.52             X2)
% 0.36/0.52          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.36/0.52          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.36/0.52          | (v2_struct_0 @ X0))),
% 0.36/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.52  thf('21', plain,
% 0.36/0.52      (((v2_struct_0 @ sk_B_1)
% 0.36/0.52        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.36/0.52        | (r2_hidden @ 
% 0.36/0.52           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.36/0.52            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ 
% 0.36/0.52             sk_A)) @ 
% 0.36/0.52           k1_xboole_0)
% 0.36/0.52        | ~ (l1_struct_0 @ sk_A)
% 0.36/0.52        | (v2_struct_0 @ sk_A))),
% 0.36/0.52      inference('sup-', [status(thm)], ['17', '20'])).
% 0.36/0.52  thf('22', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('24', plain,
% 0.36/0.52      (((v2_struct_0 @ sk_B_1)
% 0.36/0.52        | (r2_hidden @ 
% 0.36/0.52           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.36/0.52            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ 
% 0.36/0.52             sk_A)) @ 
% 0.36/0.52           k1_xboole_0)
% 0.36/0.52        | (v2_struct_0 @ sk_A))),
% 0.36/0.52      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.36/0.52  thf('25', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('26', plain,
% 0.36/0.52      (((v2_struct_0 @ sk_A)
% 0.36/0.52        | (r2_hidden @ 
% 0.36/0.52           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.36/0.52            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ 
% 0.36/0.52             sk_A)) @ 
% 0.36/0.52           k1_xboole_0))),
% 0.36/0.52      inference('clc', [status(thm)], ['24', '25'])).
% 0.36/0.52  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('28', plain,
% 0.36/0.52      ((r2_hidden @ 
% 0.36/0.52        (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.36/0.52         (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ k1_xboole_0 @ sk_B_1 @ sk_A)) @ 
% 0.36/0.52        k1_xboole_0)),
% 0.36/0.52      inference('clc', [status(thm)], ['26', '27'])).
% 0.36/0.52  thf(t4_subset_1, axiom,
% 0.36/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.52  thf('29', plain,
% 0.36/0.52      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.36/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.52  thf(t5_subset, axiom,
% 0.36/0.52    (![A:$i,B:$i,C:$i]:
% 0.36/0.52     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.36/0.52          ( v1_xboole_0 @ C ) ) ))).
% 0.36/0.52  thf('30', plain,
% 0.36/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.36/0.52         (~ (r2_hidden @ X11 @ X12)
% 0.36/0.52          | ~ (v1_xboole_0 @ X13)
% 0.36/0.52          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.36/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.36/0.52  thf('31', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]:
% 0.36/0.52         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.36/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.52  thf('32', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.36/0.52      inference('sup-', [status(thm)], ['28', '31'])).
% 0.36/0.52  thf('33', plain, ($false), inference('sup-', [status(thm)], ['0', '32'])).
% 0.36/0.52  
% 0.36/0.52  % SZS output end Refutation
% 0.36/0.52  
% 0.36/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

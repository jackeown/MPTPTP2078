%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DSJvbtB8wT

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 (  82 expanded)
%              Number of leaves         :   16 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  544 ( 943 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t11_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
              & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_tmap_1])).

thf('0',plain,
    ( ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A )
   <= ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_B )
   <= ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,
    ( ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A )
    | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('18',plain,(
    ! [X1: $i,X2: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf(t31_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( l1_pre_topc @ C )
             => ! [D: $i] :
                  ( ( l1_pre_topc @ D )
                 => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                      & ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ D ) @ ( u1_pre_topc @ D ) ) )
                      & ( m1_pre_topc @ C @ A ) )
                   => ( m1_pre_topc @ D @ B ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ( m1_pre_topc @ X7 @ X6 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) ) )
      | ~ ( m1_pre_topc @ X8 @ X9 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t31_pre_topc])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) )
       != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( m1_pre_topc @ X0 @ X3 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) @ X3 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(eq_res,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['15','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DSJvbtB8wT
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:35:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 57 iterations in 0.044s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.50  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(t11_tmap_1, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.50           ( ( v1_pre_topc @
% 0.21/0.50               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.21/0.50             ( m1_pre_topc @
% 0.21/0.50               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( l1_pre_topc @ A ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.50              ( ( v1_pre_topc @
% 0.21/0.50                  ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.21/0.50                ( m1_pre_topc @
% 0.21/0.50                  ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ 
% 0.21/0.50                  A ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t11_tmap_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      ((~ (v1_pre_topc @ 
% 0.21/0.50           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.21/0.50        | ~ (m1_pre_topc @ 
% 0.21/0.50             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((~ (m1_pre_topc @ 
% 0.21/0.50           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A))
% 0.21/0.50         <= (~
% 0.21/0.50             ((m1_pre_topc @ 
% 0.21/0.50               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ 
% 0.21/0.51               sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf(dt_u1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( m1_subset_1 @
% 0.21/0.51         ( u1_pre_topc @ A ) @ 
% 0.21/0.51         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X5 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.21/0.51          | ~ (l1_pre_topc @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.51  thf(dt_g1_pre_topc, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.51       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.21/0.51         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i]:
% 0.21/0.51         ((v1_pre_topc @ (g1_pre_topc @ X1 @ X2))
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X0)
% 0.21/0.51          | (v1_pre_topc @ 
% 0.21/0.51             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      ((~ (v1_pre_topc @ 
% 0.21/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.21/0.51         <= (~
% 0.21/0.51             ((v1_pre_topc @ 
% 0.21/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_B))
% 0.21/0.51         <= (~
% 0.21/0.51             ((v1_pre_topc @ 
% 0.21/0.51               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf('7', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_m1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.51  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (((v1_pre_topc @ 
% 0.21/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.21/0.51      inference('demod', [status(thm)], ['6', '11'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (~
% 0.21/0.51       ((m1_pre_topc @ 
% 0.21/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)) | 
% 0.21/0.51       ~
% 0.21/0.51       ((v1_pre_topc @ 
% 0.21/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (~
% 0.21/0.51       ((m1_pre_topc @ 
% 0.21/0.51         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (~ (m1_pre_topc @ 
% 0.21/0.51          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['1', '14'])).
% 0.21/0.51  thf('16', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X5 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.21/0.51          | ~ (l1_pre_topc @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i]:
% 0.21/0.51         ((l1_pre_topc @ (g1_pre_topc @ X1 @ X2))
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X0)
% 0.21/0.51          | (l1_pre_topc @ 
% 0.21/0.51             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X0)
% 0.21/0.51          | (v1_pre_topc @ 
% 0.21/0.51             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf(abstractness_v1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ( v1_pre_topc @ A ) =>
% 0.21/0.51         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_pre_topc @ X0)
% 0.21/0.51          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.51          | ~ (l1_pre_topc @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.21/0.51  thf(t31_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( l1_pre_topc @ B ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( l1_pre_topc @ C ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( l1_pre_topc @ D ) =>
% 0.21/0.51                   ( ( ( ( g1_pre_topc @
% 0.21/0.51                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.21/0.51                         ( g1_pre_topc @
% 0.21/0.51                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.21/0.51                       ( ( g1_pre_topc @
% 0.21/0.51                           ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.21/0.51                         ( g1_pre_topc @
% 0.21/0.51                           ( u1_struct_0 @ D ) @ ( u1_pre_topc @ D ) ) ) & 
% 0.21/0.51                       ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.51                     ( m1_pre_topc @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X6)
% 0.21/0.51          | ~ (l1_pre_topc @ X7)
% 0.21/0.51          | (m1_pre_topc @ X7 @ X6)
% 0.21/0.51          | ((g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8))
% 0.21/0.51              != (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.21/0.51          | ~ (m1_pre_topc @ X8 @ X9)
% 0.21/0.51          | ((g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9))
% 0.21/0.51              != (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)))
% 0.21/0.51          | ~ (l1_pre_topc @ X8)
% 0.21/0.51          | ~ (l1_pre_topc @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [t31_pre_topc])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (((g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)) != (X0))
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (v1_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X2)
% 0.21/0.51          | ~ (l1_pre_topc @ X1)
% 0.21/0.51          | ((g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2))
% 0.21/0.51              != (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.21/0.51          | ~ (m1_pre_topc @ X1 @ X2)
% 0.21/0.51          | (m1_pre_topc @ X0 @ X3)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X3))),
% 0.21/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X3)
% 0.21/0.51          | (m1_pre_topc @ 
% 0.21/0.51             (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)) @ X3)
% 0.21/0.51          | ~ (m1_pre_topc @ X1 @ X2)
% 0.21/0.51          | ((g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2))
% 0.21/0.51              != (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.21/0.51          | ~ (l1_pre_topc @ X1)
% 0.21/0.51          | ~ (l1_pre_topc @ X2)
% 0.21/0.51          | ~ (v1_pre_topc @ 
% 0.21/0.51               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.21/0.51          | ~ (l1_pre_topc @ 
% 0.21/0.51               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ 
% 0.21/0.51             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.51          | ~ (v1_pre_topc @ 
% 0.21/0.51               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.51          | ~ (l1_pre_topc @ X1)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.51          | (m1_pre_topc @ 
% 0.21/0.51             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.21/0.51          | ~ (l1_pre_topc @ X1))),
% 0.21/0.51      inference('eq_res', [status(thm)], ['24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((m1_pre_topc @ 
% 0.21/0.51           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X1)
% 0.21/0.51          | ~ (v1_pre_topc @ 
% 0.21/0.51               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.51          | ~ (l1_pre_topc @ 
% 0.21/0.51               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ 
% 0.21/0.51               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.51          | ~ (l1_pre_topc @ X1)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.51          | (m1_pre_topc @ 
% 0.21/0.51             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['20', '26'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((m1_pre_topc @ 
% 0.21/0.51           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.51          | ~ (l1_pre_topc @ X1)
% 0.21/0.51          | ~ (l1_pre_topc @ 
% 0.21/0.51               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.51          | ~ (l1_pre_topc @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X1)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.51          | (m1_pre_topc @ 
% 0.21/0.51             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['19', '28'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((m1_pre_topc @ 
% 0.21/0.51           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.51          | ~ (l1_pre_topc @ X1)
% 0.21/0.51          | ~ (l1_pre_topc @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (m1_pre_topc @ 
% 0.21/0.51           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '30'])).
% 0.21/0.51  thf('32', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      ((m1_pre_topc @ 
% 0.21/0.51        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.51  thf('35', plain, ($false), inference('demod', [status(thm)], ['15', '34'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

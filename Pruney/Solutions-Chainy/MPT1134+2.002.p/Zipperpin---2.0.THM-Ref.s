%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ufUWsAwOpw

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 (  97 expanded)
%              Number of leaves         :   16 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  546 (1062 expanded)
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

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t65_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ( ( m1_pre_topc @ A @ B )
            <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_pre_topc])).

thf('0',plain,
    ( ~ ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ~ ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_pre_topc @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
   <= ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ( m1_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('6',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( m1_pre_topc @ sk_A @ sk_B ) )
   <= ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( m1_pre_topc @ sk_A @ sk_B )
   <= ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_B )
   <= ~ ( m1_pre_topc @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( m1_pre_topc @ sk_A @ sk_B )
    | ~ ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','10'])).

thf('12',plain,(
    ~ ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','11'])).

thf('13',plain,
    ( ( m1_pre_topc @ sk_A @ sk_B )
   <= ( m1_pre_topc @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('14',plain,
    ( ( m1_pre_topc @ sk_A @ sk_B )
    | ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('15',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','10','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['13','15'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X3 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

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
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X3 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('21',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('23',plain,(
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

thf('24',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ( m1_pre_topc @ X5 @ X4 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X5 ) @ ( u1_pre_topc @ X5 ) ) )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X4 ) @ ( u1_pre_topc @ X4 ) ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t31_pre_topc])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(eq_res,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ( m1_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) )
       != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( m1_pre_topc @ X2 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_pre_topc @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['16','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['12','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ufUWsAwOpw
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:20:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 31 iterations in 0.024s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.22/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.49  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.22/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.49  thf(t65_pre_topc, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( l1_pre_topc @ B ) =>
% 0.22/0.49           ( ( m1_pre_topc @ A @ B ) <=>
% 0.22/0.49             ( m1_pre_topc @
% 0.22/0.49               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( l1_pre_topc @ A ) =>
% 0.22/0.49          ( ![B:$i]:
% 0.22/0.49            ( ( l1_pre_topc @ B ) =>
% 0.22/0.49              ( ( m1_pre_topc @ A @ B ) <=>
% 0.22/0.49                ( m1_pre_topc @
% 0.22/0.49                  A @ 
% 0.22/0.49                  ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t65_pre_topc])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      ((~ (m1_pre_topc @ sk_A @ 
% 0.22/0.49           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.22/0.49        | ~ (m1_pre_topc @ sk_A @ sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      ((~ (m1_pre_topc @ sk_A @ 
% 0.22/0.49           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.22/0.49         <= (~
% 0.22/0.49             ((m1_pre_topc @ sk_A @ 
% 0.22/0.49               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (~
% 0.22/0.49       ((m1_pre_topc @ sk_A @ 
% 0.22/0.49         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))) | 
% 0.22/0.49       ~ ((m1_pre_topc @ sk_A @ sk_B))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (((m1_pre_topc @ sk_A @ 
% 0.22/0.49         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.22/0.49        | (m1_pre_topc @ sk_A @ sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (((m1_pre_topc @ sk_A @ 
% 0.22/0.49         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))
% 0.22/0.49         <= (((m1_pre_topc @ sk_A @ 
% 0.22/0.49               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf(t59_pre_topc, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_pre_topc @
% 0.22/0.49             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.22/0.49           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X8 : $i, X9 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X8 @ 
% 0.22/0.49             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.22/0.49          | (m1_pre_topc @ X8 @ X9)
% 0.22/0.49          | ~ (l1_pre_topc @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (((~ (l1_pre_topc @ sk_B) | (m1_pre_topc @ sk_A @ sk_B)))
% 0.22/0.49         <= (((m1_pre_topc @ sk_A @ 
% 0.22/0.49               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.49  thf('7', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (((m1_pre_topc @ sk_A @ sk_B))
% 0.22/0.49         <= (((m1_pre_topc @ sk_A @ 
% 0.22/0.49               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))))),
% 0.22/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      ((~ (m1_pre_topc @ sk_A @ sk_B)) <= (~ ((m1_pre_topc @ sk_A @ sk_B)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (((m1_pre_topc @ sk_A @ sk_B)) | 
% 0.22/0.49       ~
% 0.22/0.49       ((m1_pre_topc @ sk_A @ 
% 0.22/0.49         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (~
% 0.22/0.49       ((m1_pre_topc @ sk_A @ 
% 0.22/0.49         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['2', '10'])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (~ (m1_pre_topc @ sk_A @ 
% 0.22/0.49          (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['1', '11'])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (((m1_pre_topc @ sk_A @ sk_B)) <= (((m1_pre_topc @ sk_A @ sk_B)))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (((m1_pre_topc @ sk_A @ sk_B)) | 
% 0.22/0.49       ((m1_pre_topc @ sk_A @ 
% 0.22/0.49         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf('15', plain, (((m1_pre_topc @ sk_A @ sk_B))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['2', '10', '14'])).
% 0.22/0.49  thf('16', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['13', '15'])).
% 0.22/0.49  thf(dt_u1_pre_topc, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( m1_subset_1 @
% 0.22/0.49         ( u1_pre_topc @ A ) @ 
% 0.22/0.49         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X3 : $i]:
% 0.22/0.49         ((m1_subset_1 @ (u1_pre_topc @ X3) @ 
% 0.22/0.49           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3))))
% 0.22/0.49          | ~ (l1_pre_topc @ X3))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.22/0.49  thf(dt_g1_pre_topc, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.49       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.22/0.49         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X1 : $i, X2 : $i]:
% 0.22/0.49         ((l1_pre_topc @ (g1_pre_topc @ X1 @ X2))
% 0.22/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X0)
% 0.22/0.49          | (l1_pre_topc @ 
% 0.22/0.49             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X3 : $i]:
% 0.22/0.49         ((m1_subset_1 @ (u1_pre_topc @ X3) @ 
% 0.22/0.49           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3))))
% 0.22/0.49          | ~ (l1_pre_topc @ X3))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X1 : $i, X2 : $i]:
% 0.22/0.49         ((v1_pre_topc @ (g1_pre_topc @ X1 @ X2))
% 0.22/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X0)
% 0.22/0.49          | (v1_pre_topc @ 
% 0.22/0.49             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.49  thf(abstractness_v1_pre_topc, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ( v1_pre_topc @ A ) =>
% 0.22/0.49         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_pre_topc @ X0)
% 0.22/0.49          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.49          | ~ (l1_pre_topc @ X0))),
% 0.22/0.49      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.22/0.49  thf(t31_pre_topc, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( l1_pre_topc @ B ) =>
% 0.22/0.49           ( ![C:$i]:
% 0.22/0.49             ( ( l1_pre_topc @ C ) =>
% 0.22/0.49               ( ![D:$i]:
% 0.22/0.49                 ( ( l1_pre_topc @ D ) =>
% 0.22/0.49                   ( ( ( ( g1_pre_topc @
% 0.22/0.49                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.22/0.49                         ( g1_pre_topc @
% 0.22/0.49                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.22/0.49                       ( ( g1_pre_topc @
% 0.22/0.49                           ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.22/0.49                         ( g1_pre_topc @
% 0.22/0.49                           ( u1_struct_0 @ D ) @ ( u1_pre_topc @ D ) ) ) & 
% 0.22/0.49                       ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.49                     ( m1_pre_topc @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X4)
% 0.22/0.49          | ~ (l1_pre_topc @ X5)
% 0.22/0.49          | (m1_pre_topc @ X5 @ X4)
% 0.22/0.49          | ((g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6))
% 0.22/0.49              != (g1_pre_topc @ (u1_struct_0 @ X5) @ (u1_pre_topc @ X5)))
% 0.22/0.49          | ~ (m1_pre_topc @ X6 @ X7)
% 0.22/0.49          | ((g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7))
% 0.22/0.49              != (g1_pre_topc @ (u1_struct_0 @ X4) @ (u1_pre_topc @ X4)))
% 0.22/0.49          | ~ (l1_pre_topc @ X6)
% 0.22/0.49          | ~ (l1_pre_topc @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [t31_pre_topc])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X0)
% 0.22/0.49          | ~ (l1_pre_topc @ X1)
% 0.22/0.49          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.22/0.49              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.22/0.49          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.49          | (m1_pre_topc @ X1 @ X2)
% 0.22/0.49          | ~ (l1_pre_topc @ X1)
% 0.22/0.49          | ~ (l1_pre_topc @ X2))),
% 0.22/0.49      inference('eq_res', [status(thm)], ['24'])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X2)
% 0.22/0.49          | (m1_pre_topc @ X1 @ X2)
% 0.22/0.49          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.49          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.22/0.49              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.22/0.49          | ~ (l1_pre_topc @ X1)
% 0.22/0.49          | ~ (l1_pre_topc @ X0))),
% 0.22/0.49      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (((g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)) != (X0))
% 0.22/0.49          | ~ (l1_pre_topc @ X0)
% 0.22/0.49          | ~ (v1_pre_topc @ X0)
% 0.22/0.49          | ~ (l1_pre_topc @ X1)
% 0.22/0.49          | ~ (l1_pre_topc @ X2)
% 0.22/0.49          | ~ (m1_pre_topc @ X2 @ X1)
% 0.22/0.49          | (m1_pre_topc @ X2 @ X0)
% 0.22/0.49          | ~ (l1_pre_topc @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['23', '26'])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X1 : $i, X2 : $i]:
% 0.22/0.49         ((m1_pre_topc @ X2 @ 
% 0.22/0.49           (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.22/0.49          | ~ (m1_pre_topc @ X2 @ X1)
% 0.22/0.49          | ~ (l1_pre_topc @ X2)
% 0.22/0.49          | ~ (l1_pre_topc @ X1)
% 0.22/0.49          | ~ (v1_pre_topc @ 
% 0.22/0.49               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.22/0.49          | ~ (l1_pre_topc @ 
% 0.22/0.49               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['27'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X0)
% 0.22/0.49          | ~ (l1_pre_topc @ 
% 0.22/0.49               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.49          | ~ (l1_pre_topc @ X0)
% 0.22/0.49          | ~ (l1_pre_topc @ X1)
% 0.22/0.49          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.49          | (m1_pre_topc @ X1 @ 
% 0.22/0.49             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['22', '28'])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((m1_pre_topc @ X1 @ 
% 0.22/0.49           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.49          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.49          | ~ (l1_pre_topc @ X1)
% 0.22/0.49          | ~ (l1_pre_topc @ 
% 0.22/0.49               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.49          | ~ (l1_pre_topc @ X0))),
% 0.22/0.49      inference('simplify', [status(thm)], ['29'])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X0)
% 0.22/0.49          | ~ (l1_pre_topc @ X0)
% 0.22/0.49          | ~ (l1_pre_topc @ X1)
% 0.22/0.49          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.49          | (m1_pre_topc @ X1 @ 
% 0.22/0.49             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['19', '30'])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((m1_pre_topc @ X1 @ 
% 0.22/0.49           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.49          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.49          | ~ (l1_pre_topc @ X1)
% 0.22/0.49          | ~ (l1_pre_topc @ X0))),
% 0.22/0.49      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      ((~ (l1_pre_topc @ sk_B)
% 0.22/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.49        | (m1_pre_topc @ sk_A @ 
% 0.22/0.49           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['16', '32'])).
% 0.22/0.49  thf('34', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      ((m1_pre_topc @ sk_A @ 
% 0.22/0.49        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.22/0.49  thf('37', plain, ($false), inference('demod', [status(thm)], ['12', '36'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

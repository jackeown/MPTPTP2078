%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1JGWkkje5u

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:07 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 116 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  503 (1592 expanded)
%              Number of equality atoms :   16 (  59 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t12_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( B
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
               => ( ( m1_pre_topc @ B @ A )
                <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v2_pre_topc @ C )
                  & ( l1_pre_topc @ C ) )
               => ( ( B
                    = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
                 => ( ( m1_pre_topc @ B @ A )
                  <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_tmap_1])).

thf('0',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
   <= ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( u1_pre_topc @ X6 ) ) @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('6',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','11'])).

thf('13',plain,(
    ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','12'])).

thf('14',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('15',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
    | ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('16',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','11','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['14','16'])).

thf('18',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('19',plain,(
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

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 )
      | ( m1_pre_topc @ X3 @ X2 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X4 ) @ ( u1_pre_topc @ X4 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( m1_pre_topc @ X4 @ X5 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X5 ) @ ( u1_pre_topc @ X5 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t31_pre_topc])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( m1_pre_topc @ X1 @ X3 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_pre_topc @ X1 @ X3 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) @ X2 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ X0 )
      | ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X1: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('28',plain,
    ( ( v1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( sk_B
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['25','31','32','33','34','35'])).

thf('37',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['13','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1JGWkkje5u
% 0.15/0.38  % Computer   : n011.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 13:07:12 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.25/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.49  % Solved by: fo/fo7.sh
% 0.25/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.49  % done 77 iterations in 0.039s
% 0.25/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.49  % SZS output start Refutation
% 0.25/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.25/0.49  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.25/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.25/0.49  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.25/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.25/0.49  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.25/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.25/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.25/0.49  thf(t12_tmap_1, conjecture,
% 0.25/0.49    (![A:$i]:
% 0.25/0.49     ( ( l1_pre_topc @ A ) =>
% 0.25/0.49       ( ![B:$i]:
% 0.25/0.49         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.25/0.49           ( ![C:$i]:
% 0.25/0.49             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.25/0.49               ( ( ( B ) =
% 0.25/0.49                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.25/0.49                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.25/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.49    (~( ![A:$i]:
% 0.25/0.49        ( ( l1_pre_topc @ A ) =>
% 0.25/0.49          ( ![B:$i]:
% 0.25/0.49            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.25/0.49              ( ![C:$i]:
% 0.25/0.49                ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.25/0.49                  ( ( ( B ) =
% 0.25/0.49                      ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.25/0.49                    ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) )),
% 0.25/0.49    inference('cnf.neg', [status(esa)], [t12_tmap_1])).
% 0.25/0.49  thf('0', plain,
% 0.25/0.49      ((~ (m1_pre_topc @ sk_C @ sk_A) | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.25/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.49  thf('1', plain,
% 0.25/0.49      ((~ (m1_pre_topc @ sk_C @ sk_A)) <= (~ ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.25/0.49      inference('split', [status(esa)], ['0'])).
% 0.25/0.49  thf('2', plain,
% 0.25/0.49      (~ ((m1_pre_topc @ sk_C @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.25/0.49      inference('split', [status(esa)], ['0'])).
% 0.25/0.49  thf('3', plain,
% 0.25/0.49      (((m1_pre_topc @ sk_C @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.25/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.49  thf('4', plain,
% 0.25/0.49      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.25/0.49      inference('split', [status(esa)], ['3'])).
% 0.25/0.49  thf(t11_tmap_1, axiom,
% 0.25/0.49    (![A:$i]:
% 0.25/0.49     ( ( l1_pre_topc @ A ) =>
% 0.25/0.49       ( ![B:$i]:
% 0.25/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.25/0.49           ( ( v1_pre_topc @
% 0.25/0.49               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.25/0.49             ( m1_pre_topc @
% 0.25/0.49               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 0.25/0.49  thf('5', plain,
% 0.25/0.49      (![X6 : $i, X7 : $i]:
% 0.25/0.49         (~ (m1_pre_topc @ X6 @ X7)
% 0.25/0.49          | (m1_pre_topc @ 
% 0.25/0.49             (g1_pre_topc @ (u1_struct_0 @ X6) @ (u1_pre_topc @ X6)) @ X7)
% 0.25/0.49          | ~ (l1_pre_topc @ X7))),
% 0.25/0.49      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.25/0.49  thf('6', plain,
% 0.25/0.49      (((~ (l1_pre_topc @ sk_A)
% 0.25/0.49         | (m1_pre_topc @ 
% 0.25/0.49            (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_A)))
% 0.25/0.49         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.25/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.25/0.49  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.49  thf('8', plain,
% 0.25/0.49      (((sk_B) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.25/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.49  thf('9', plain,
% 0.25/0.49      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.25/0.49      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.25/0.49  thf('10', plain,
% 0.25/0.49      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.25/0.49      inference('split', [status(esa)], ['0'])).
% 0.25/0.49  thf('11', plain,
% 0.25/0.49      (((m1_pre_topc @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_C @ sk_A))),
% 0.25/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.25/0.49  thf('12', plain, (~ ((m1_pre_topc @ sk_C @ sk_A))),
% 0.25/0.49      inference('sat_resolution*', [status(thm)], ['2', '11'])).
% 0.25/0.49  thf('13', plain, (~ (m1_pre_topc @ sk_C @ sk_A)),
% 0.25/0.49      inference('simpl_trail', [status(thm)], ['1', '12'])).
% 0.25/0.49  thf('14', plain,
% 0.25/0.49      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.25/0.49      inference('split', [status(esa)], ['3'])).
% 0.25/0.49  thf('15', plain,
% 0.25/0.49      (((m1_pre_topc @ sk_B @ sk_A)) | ((m1_pre_topc @ sk_C @ sk_A))),
% 0.25/0.49      inference('split', [status(esa)], ['3'])).
% 0.25/0.49  thf('16', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.25/0.49      inference('sat_resolution*', [status(thm)], ['2', '11', '15'])).
% 0.25/0.49  thf('17', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.25/0.49      inference('simpl_trail', [status(thm)], ['14', '16'])).
% 0.25/0.49  thf('18', plain,
% 0.25/0.49      (((sk_B) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.25/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.49  thf(abstractness_v1_pre_topc, axiom,
% 0.25/0.49    (![A:$i]:
% 0.25/0.49     ( ( l1_pre_topc @ A ) =>
% 0.25/0.49       ( ( v1_pre_topc @ A ) =>
% 0.25/0.49         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.25/0.49  thf('19', plain,
% 0.25/0.49      (![X0 : $i]:
% 0.25/0.49         (~ (v1_pre_topc @ X0)
% 0.25/0.49          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.25/0.49          | ~ (l1_pre_topc @ X0))),
% 0.25/0.49      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.25/0.49  thf(t31_pre_topc, axiom,
% 0.25/0.49    (![A:$i]:
% 0.25/0.49     ( ( l1_pre_topc @ A ) =>
% 0.25/0.49       ( ![B:$i]:
% 0.25/0.49         ( ( l1_pre_topc @ B ) =>
% 0.25/0.49           ( ![C:$i]:
% 0.25/0.49             ( ( l1_pre_topc @ C ) =>
% 0.25/0.49               ( ![D:$i]:
% 0.25/0.49                 ( ( l1_pre_topc @ D ) =>
% 0.25/0.49                   ( ( ( ( g1_pre_topc @
% 0.25/0.49                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.25/0.49                         ( g1_pre_topc @
% 0.25/0.49                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.25/0.49                       ( ( g1_pre_topc @
% 0.25/0.49                           ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.25/0.49                         ( g1_pre_topc @
% 0.25/0.49                           ( u1_struct_0 @ D ) @ ( u1_pre_topc @ D ) ) ) & 
% 0.25/0.49                       ( m1_pre_topc @ C @ A ) ) =>
% 0.25/0.49                     ( m1_pre_topc @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.25/0.49  thf('20', plain,
% 0.25/0.49      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.25/0.49         (~ (l1_pre_topc @ X2)
% 0.25/0.49          | ~ (l1_pre_topc @ X3)
% 0.25/0.49          | (m1_pre_topc @ X3 @ X2)
% 0.25/0.49          | ((g1_pre_topc @ (u1_struct_0 @ X4) @ (u1_pre_topc @ X4))
% 0.25/0.49              != (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.25/0.49          | ~ (m1_pre_topc @ X4 @ X5)
% 0.25/0.49          | ((g1_pre_topc @ (u1_struct_0 @ X5) @ (u1_pre_topc @ X5))
% 0.25/0.49              != (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.25/0.49          | ~ (l1_pre_topc @ X4)
% 0.25/0.49          | ~ (l1_pre_topc @ X5))),
% 0.25/0.49      inference('cnf', [status(esa)], [t31_pre_topc])).
% 0.25/0.49  thf('21', plain,
% 0.25/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.49         (((X0) != (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.25/0.49          | ~ (l1_pre_topc @ X0)
% 0.25/0.49          | ~ (v1_pre_topc @ X0)
% 0.25/0.49          | ~ (l1_pre_topc @ X2)
% 0.25/0.49          | ~ (l1_pre_topc @ X0)
% 0.25/0.49          | ((g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2))
% 0.25/0.49              != (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.25/0.49          | ~ (m1_pre_topc @ X0 @ X2)
% 0.25/0.49          | (m1_pre_topc @ X1 @ X3)
% 0.25/0.49          | ~ (l1_pre_topc @ X1)
% 0.25/0.49          | ~ (l1_pre_topc @ X3))),
% 0.25/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.25/0.49  thf('22', plain,
% 0.25/0.49      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.49         (~ (l1_pre_topc @ X3)
% 0.25/0.49          | ~ (l1_pre_topc @ X1)
% 0.25/0.49          | (m1_pre_topc @ X1 @ X3)
% 0.25/0.49          | ~ (m1_pre_topc @ 
% 0.25/0.49               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)) @ X2)
% 0.25/0.49          | ((g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2))
% 0.25/0.49              != (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.25/0.49          | ~ (l1_pre_topc @ X2)
% 0.25/0.49          | ~ (v1_pre_topc @ 
% 0.25/0.49               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.25/0.49          | ~ (l1_pre_topc @ 
% 0.25/0.49               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))))),
% 0.25/0.49      inference('simplify', [status(thm)], ['21'])).
% 0.25/0.49  thf('23', plain,
% 0.25/0.49      (![X0 : $i, X1 : $i]:
% 0.25/0.49         (~ (l1_pre_topc @ 
% 0.25/0.49             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.25/0.49          | ~ (v1_pre_topc @ 
% 0.25/0.49               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.25/0.49          | ~ (l1_pre_topc @ X1)
% 0.25/0.49          | ~ (m1_pre_topc @ 
% 0.25/0.49               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.25/0.49          | (m1_pre_topc @ X0 @ X1)
% 0.25/0.49          | ~ (l1_pre_topc @ X0)
% 0.25/0.49          | ~ (l1_pre_topc @ X1))),
% 0.25/0.49      inference('eq_res', [status(thm)], ['22'])).
% 0.25/0.49  thf('24', plain,
% 0.25/0.49      (![X0 : $i, X1 : $i]:
% 0.25/0.49         (~ (l1_pre_topc @ X0)
% 0.25/0.49          | (m1_pre_topc @ X0 @ X1)
% 0.25/0.49          | ~ (m1_pre_topc @ 
% 0.25/0.49               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.25/0.49          | ~ (l1_pre_topc @ X1)
% 0.25/0.49          | ~ (v1_pre_topc @ 
% 0.25/0.49               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.25/0.49          | ~ (l1_pre_topc @ 
% 0.25/0.49               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.25/0.49      inference('simplify', [status(thm)], ['23'])).
% 0.25/0.49  thf('25', plain,
% 0.25/0.49      (![X0 : $i]:
% 0.25/0.49         (~ (v1_pre_topc @ sk_B)
% 0.25/0.49          | ~ (l1_pre_topc @ 
% 0.25/0.49               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.25/0.49          | ~ (l1_pre_topc @ X0)
% 0.25/0.49          | ~ (m1_pre_topc @ 
% 0.25/0.49               (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ X0)
% 0.25/0.49          | (m1_pre_topc @ sk_C @ X0)
% 0.25/0.49          | ~ (l1_pre_topc @ sk_C))),
% 0.25/0.49      inference('sup-', [status(thm)], ['18', '24'])).
% 0.25/0.49  thf('26', plain,
% 0.25/0.49      (((sk_B) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.25/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.49  thf(fc6_pre_topc, axiom,
% 0.25/0.49    (![A:$i]:
% 0.25/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.49       ( ( v1_pre_topc @
% 0.25/0.49           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.25/0.49         ( v2_pre_topc @
% 0.25/0.49           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.25/0.49  thf('27', plain,
% 0.25/0.49      (![X1 : $i]:
% 0.25/0.49         ((v1_pre_topc @ 
% 0.25/0.49           (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.25/0.49          | ~ (l1_pre_topc @ X1)
% 0.25/0.49          | ~ (v2_pre_topc @ X1))),
% 0.25/0.49      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.25/0.49  thf('28', plain,
% 0.25/0.49      (((v1_pre_topc @ sk_B) | ~ (v2_pre_topc @ sk_C) | ~ (l1_pre_topc @ sk_C))),
% 0.25/0.49      inference('sup+', [status(thm)], ['26', '27'])).
% 0.25/0.49  thf('29', plain, ((v2_pre_topc @ sk_C)),
% 0.25/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.49  thf('30', plain, ((l1_pre_topc @ sk_C)),
% 0.25/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.49  thf('31', plain, ((v1_pre_topc @ sk_B)),
% 0.25/0.49      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.25/0.49  thf('32', plain,
% 0.25/0.49      (((sk_B) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.25/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.49  thf('33', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.49  thf('34', plain,
% 0.25/0.49      (((sk_B) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.25/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.49  thf('35', plain, ((l1_pre_topc @ sk_C)),
% 0.25/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.49  thf('36', plain,
% 0.25/0.49      (![X0 : $i]:
% 0.25/0.49         (~ (l1_pre_topc @ X0)
% 0.25/0.49          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.25/0.49          | (m1_pre_topc @ sk_C @ X0))),
% 0.25/0.49      inference('demod', [status(thm)], ['25', '31', '32', '33', '34', '35'])).
% 0.25/0.49  thf('37', plain, (((m1_pre_topc @ sk_C @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.25/0.49      inference('sup-', [status(thm)], ['17', '36'])).
% 0.25/0.49  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.49  thf('39', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.25/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.25/0.49  thf('40', plain, ($false), inference('demod', [status(thm)], ['13', '39'])).
% 0.25/0.49  
% 0.25/0.49  % SZS output end Refutation
% 0.25/0.49  
% 0.25/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

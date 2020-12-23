%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oNA1zeWtVQ

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:10 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 128 expanded)
%              Number of leaves         :   22 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :  505 (1118 expanded)
%              Number of equality atoms :   31 (  83 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t95_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k7_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('3',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k7_relat_1 @ X39 @ X38 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X38 ) @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('4',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('7',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('8',plain,(
    ! [X34: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t67_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k5_relat_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('9',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( ( k5_relat_1 @ X32 @ X31 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k2_relat_1 @ X32 ) @ ( k1_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t67_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('11',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['3','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k7_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','21'])).

thf('23',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','22'])).

thf('24',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('25',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('26',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','21','25'])).

thf('27',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['24','26'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('30',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( r2_hidden @ X35 @ ( k1_relat_1 @ X37 ) )
      | ( r2_hidden @ X35 @ ( k1_relat_1 @ ( k7_relat_1 @ X37 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('40',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('41',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['23','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oNA1zeWtVQ
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:02:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.67/0.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.67/0.85  % Solved by: fo/fo7.sh
% 0.67/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.85  % done 950 iterations in 0.399s
% 0.67/0.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.67/0.85  % SZS output start Refutation
% 0.67/0.85  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.67/0.85  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.67/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.85  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.67/0.85  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.67/0.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.85  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.67/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.85  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.67/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.85  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.67/0.85  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.67/0.85  thf(t95_relat_1, conjecture,
% 0.67/0.85    (![A:$i,B:$i]:
% 0.67/0.85     ( ( v1_relat_1 @ B ) =>
% 0.67/0.85       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.67/0.85         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.67/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.85    (~( ![A:$i,B:$i]:
% 0.67/0.85        ( ( v1_relat_1 @ B ) =>
% 0.67/0.85          ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.67/0.85            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.67/0.85    inference('cnf.neg', [status(esa)], [t95_relat_1])).
% 0.67/0.85  thf('0', plain,
% 0.67/0.85      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.67/0.85        | ((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('1', plain,
% 0.67/0.85      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.67/0.85         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.67/0.85      inference('split', [status(esa)], ['0'])).
% 0.67/0.85  thf('2', plain,
% 0.67/0.85      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.67/0.85       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.67/0.85      inference('split', [status(esa)], ['0'])).
% 0.67/0.85  thf(t94_relat_1, axiom,
% 0.67/0.85    (![A:$i,B:$i]:
% 0.67/0.85     ( ( v1_relat_1 @ B ) =>
% 0.67/0.85       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.67/0.85  thf('3', plain,
% 0.67/0.85      (![X38 : $i, X39 : $i]:
% 0.67/0.85         (((k7_relat_1 @ X39 @ X38) = (k5_relat_1 @ (k6_relat_1 @ X38) @ X39))
% 0.67/0.85          | ~ (v1_relat_1 @ X39))),
% 0.67/0.85      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.67/0.85  thf('4', plain,
% 0.67/0.85      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.67/0.85        | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('5', plain,
% 0.67/0.85      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.67/0.85         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.67/0.85      inference('split', [status(esa)], ['4'])).
% 0.67/0.85  thf(symmetry_r1_xboole_0, axiom,
% 0.67/0.85    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.67/0.85  thf('6', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.67/0.85      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.67/0.85  thf('7', plain,
% 0.67/0.85      (((r1_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.67/0.85         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.67/0.85      inference('sup-', [status(thm)], ['5', '6'])).
% 0.67/0.85  thf(t71_relat_1, axiom,
% 0.67/0.85    (![A:$i]:
% 0.67/0.85     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.67/0.85       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.67/0.85  thf('8', plain, (![X34 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X34)) = (X34))),
% 0.67/0.85      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.67/0.85  thf(t67_relat_1, axiom,
% 0.67/0.85    (![A:$i]:
% 0.67/0.85     ( ( v1_relat_1 @ A ) =>
% 0.67/0.85       ( ![B:$i]:
% 0.67/0.85         ( ( v1_relat_1 @ B ) =>
% 0.67/0.85           ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.67/0.85             ( ( k5_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.67/0.85  thf('9', plain,
% 0.67/0.85      (![X31 : $i, X32 : $i]:
% 0.67/0.85         (~ (v1_relat_1 @ X31)
% 0.67/0.85          | ((k5_relat_1 @ X32 @ X31) = (k1_xboole_0))
% 0.67/0.85          | ~ (r1_xboole_0 @ (k2_relat_1 @ X32) @ (k1_relat_1 @ X31))
% 0.67/0.85          | ~ (v1_relat_1 @ X32))),
% 0.67/0.85      inference('cnf', [status(esa)], [t67_relat_1])).
% 0.67/0.85  thf('10', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         (~ (r1_xboole_0 @ X0 @ (k1_relat_1 @ X1))
% 0.67/0.85          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.67/0.85          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k1_xboole_0))
% 0.67/0.85          | ~ (v1_relat_1 @ X1))),
% 0.67/0.85      inference('sup-', [status(thm)], ['8', '9'])).
% 0.67/0.85  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.67/0.85  thf('11', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.67/0.85      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.67/0.85  thf('12', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         (~ (r1_xboole_0 @ X0 @ (k1_relat_1 @ X1))
% 0.67/0.85          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k1_xboole_0))
% 0.67/0.85          | ~ (v1_relat_1 @ X1))),
% 0.67/0.85      inference('demod', [status(thm)], ['10', '11'])).
% 0.67/0.85  thf('13', plain,
% 0.67/0.85      (((~ (v1_relat_1 @ sk_B)
% 0.67/0.85         | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (k1_xboole_0))))
% 0.67/0.85         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.67/0.85      inference('sup-', [status(thm)], ['7', '12'])).
% 0.67/0.85  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('15', plain,
% 0.67/0.85      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.67/0.85         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.67/0.85      inference('demod', [status(thm)], ['13', '14'])).
% 0.67/0.85  thf('16', plain,
% 0.67/0.85      (((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B)))
% 0.67/0.85         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.67/0.85      inference('sup+', [status(thm)], ['3', '15'])).
% 0.67/0.85  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('18', plain,
% 0.67/0.85      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.67/0.85         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.67/0.85      inference('demod', [status(thm)], ['16', '17'])).
% 0.67/0.85  thf('19', plain,
% 0.67/0.85      ((((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.67/0.85         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.67/0.85      inference('split', [status(esa)], ['0'])).
% 0.67/0.85  thf('20', plain,
% 0.67/0.85      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.67/0.85         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.67/0.85             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.67/0.85      inference('sup-', [status(thm)], ['18', '19'])).
% 0.67/0.85  thf('21', plain,
% 0.67/0.85      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.67/0.85       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.67/0.85      inference('simplify', [status(thm)], ['20'])).
% 0.67/0.85  thf('22', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.67/0.85      inference('sat_resolution*', [status(thm)], ['2', '21'])).
% 0.67/0.85  thf('23', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.67/0.85      inference('simpl_trail', [status(thm)], ['1', '22'])).
% 0.67/0.85  thf('24', plain,
% 0.67/0.85      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.67/0.85         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.67/0.85      inference('split', [status(esa)], ['4'])).
% 0.67/0.85  thf('25', plain,
% 0.67/0.85      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.67/0.85       ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.67/0.85      inference('split', [status(esa)], ['4'])).
% 0.67/0.85  thf('26', plain, ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.67/0.85      inference('sat_resolution*', [status(thm)], ['2', '21', '25'])).
% 0.67/0.85  thf('27', plain, (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.67/0.85      inference('simpl_trail', [status(thm)], ['24', '26'])).
% 0.67/0.85  thf(t3_xboole_0, axiom,
% 0.67/0.85    (![A:$i,B:$i]:
% 0.67/0.85     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.67/0.85            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.67/0.85       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.67/0.85            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.67/0.85  thf('28', plain,
% 0.67/0.85      (![X2 : $i, X3 : $i]:
% 0.67/0.85         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X3))),
% 0.67/0.85      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.67/0.85  thf('29', plain,
% 0.67/0.85      (![X2 : $i, X3 : $i]:
% 0.67/0.85         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X2))),
% 0.67/0.85      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.67/0.85  thf(t86_relat_1, axiom,
% 0.67/0.85    (![A:$i,B:$i,C:$i]:
% 0.67/0.85     ( ( v1_relat_1 @ C ) =>
% 0.67/0.85       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.67/0.85         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.67/0.85  thf('30', plain,
% 0.67/0.85      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.67/0.85         (~ (r2_hidden @ X35 @ X36)
% 0.67/0.85          | ~ (r2_hidden @ X35 @ (k1_relat_1 @ X37))
% 0.67/0.85          | (r2_hidden @ X35 @ (k1_relat_1 @ (k7_relat_1 @ X37 @ X36)))
% 0.67/0.85          | ~ (v1_relat_1 @ X37))),
% 0.67/0.85      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.67/0.85  thf('31', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.85         ((r1_xboole_0 @ (k1_relat_1 @ X0) @ X1)
% 0.67/0.85          | ~ (v1_relat_1 @ X0)
% 0.67/0.85          | (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.67/0.85             (k1_relat_1 @ (k7_relat_1 @ X0 @ X2)))
% 0.67/0.85          | ~ (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X2))),
% 0.67/0.85      inference('sup-', [status(thm)], ['29', '30'])).
% 0.67/0.85  thf('32', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ X0)
% 0.67/0.85          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ 
% 0.67/0.85             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.67/0.85          | ~ (v1_relat_1 @ X1)
% 0.67/0.85          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 0.67/0.85      inference('sup-', [status(thm)], ['28', '31'])).
% 0.67/0.85  thf('33', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         (~ (v1_relat_1 @ X1)
% 0.67/0.85          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ 
% 0.67/0.85             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.67/0.85          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 0.67/0.85      inference('simplify', [status(thm)], ['32'])).
% 0.67/0.85  thf('34', plain,
% 0.67/0.85      (![X2 : $i, X3 : $i]:
% 0.67/0.85         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X3))),
% 0.67/0.85      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.67/0.85  thf('35', plain,
% 0.67/0.85      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.67/0.85         (~ (r2_hidden @ X4 @ X2)
% 0.67/0.85          | ~ (r2_hidden @ X4 @ X5)
% 0.67/0.85          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.67/0.85      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.67/0.85  thf('36', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.85         ((r1_xboole_0 @ X1 @ X0)
% 0.67/0.85          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.67/0.85          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.67/0.85      inference('sup-', [status(thm)], ['34', '35'])).
% 0.67/0.85  thf('37', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ X0)
% 0.67/0.85          | ~ (v1_relat_1 @ X1)
% 0.67/0.85          | ~ (r1_xboole_0 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.67/0.85          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 0.67/0.85      inference('sup-', [status(thm)], ['33', '36'])).
% 0.67/0.85  thf('38', plain,
% 0.67/0.85      (![X0 : $i, X1 : $i]:
% 0.67/0.85         (~ (r1_xboole_0 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.67/0.85          | ~ (v1_relat_1 @ X1)
% 0.67/0.85          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 0.67/0.85      inference('simplify', [status(thm)], ['37'])).
% 0.67/0.85  thf('39', plain,
% 0.67/0.85      ((~ (r1_xboole_0 @ sk_A @ (k1_relat_1 @ k1_xboole_0))
% 0.67/0.85        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.67/0.85        | ~ (v1_relat_1 @ sk_B))),
% 0.67/0.85      inference('sup-', [status(thm)], ['27', '38'])).
% 0.67/0.85  thf(t60_relat_1, axiom,
% 0.67/0.85    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.67/0.85     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.67/0.85  thf('40', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.85      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.67/0.85  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.67/0.85  thf('41', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.67/0.85      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.67/0.85  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('43', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.67/0.85      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.67/0.85  thf('44', plain, ($false), inference('demod', [status(thm)], ['23', '43'])).
% 0.67/0.85  
% 0.67/0.85  % SZS output end Refutation
% 0.67/0.85  
% 0.72/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

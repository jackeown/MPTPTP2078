%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q6yd4TFHkg

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:05 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   57 (  72 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  447 ( 677 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t125_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_xboole_0 @ A @ B )
          & ( v2_funct_1 @ C ) )
       => ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_xboole_0 @ A @ B )
            & ( v2_funct_1 @ C ) )
         => ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t125_funct_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t121_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
          = ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k9_relat_1 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X12 @ X13 ) @ ( k9_relat_1 @ X12 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k9_relat_1 @ X2 @ X0 ) @ ( k9_relat_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k9_relat_1 @ X0 @ sk_B ) @ ( k9_relat_1 @ X0 @ sk_A ) ) @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t149_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X11: $i] :
      ( ( ( k9_relat_1 @ X11 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t149_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k9_relat_1 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X12 @ X13 ) @ ( k9_relat_1 @ X12 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf('14',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( r1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X9: $i] :
      ( ( r1_xboole_0 @ X9 @ X9 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('19',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('21',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('22',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ~ ( r1_xboole_0 @ ( k9_relat_1 @ sk_C_2 @ sk_A ) @ ( k9_relat_1 @ sk_C_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v2_funct_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['31','32','33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q6yd4TFHkg
% 0.16/0.38  % Computer   : n023.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 18:18:36 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.24/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.53  % Solved by: fo/fo7.sh
% 0.24/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.53  % done 77 iterations in 0.038s
% 0.24/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.53  % SZS output start Refutation
% 0.24/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.53  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.24/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.53  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.24/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.24/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.24/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.24/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.24/0.53  thf(t125_funct_1, conjecture,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.24/0.53       ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.24/0.53         ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.24/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.53        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.24/0.53          ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.24/0.53            ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.24/0.53    inference('cnf.neg', [status(esa)], [t125_funct_1])).
% 0.24/0.53  thf('0', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(t3_xboole_0, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.24/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.24/0.53            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.24/0.53  thf('1', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]:
% 0.24/0.53         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.24/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.24/0.53  thf(t4_xboole_0, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.24/0.53            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.24/0.53  thf('2', plain,
% 0.24/0.53      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.24/0.53          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.24/0.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.24/0.53  thf('3', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.53         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.24/0.53          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.53  thf('4', plain,
% 0.24/0.53      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)),
% 0.24/0.53      inference('sup-', [status(thm)], ['0', '3'])).
% 0.24/0.53  thf(t66_xboole_1, axiom,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.24/0.53       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.24/0.53  thf('5', plain,
% 0.24/0.53      (![X10 : $i]: (((X10) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X10 @ X10))),
% 0.24/0.53      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.24/0.53  thf('6', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.53  thf(t121_funct_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.24/0.53       ( ( v2_funct_1 @ C ) =>
% 0.24/0.53         ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.24/0.53           ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.24/0.53  thf('7', plain,
% 0.24/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.24/0.53         (~ (v2_funct_1 @ X12)
% 0.24/0.53          | ((k9_relat_1 @ X12 @ (k3_xboole_0 @ X13 @ X14))
% 0.24/0.53              = (k3_xboole_0 @ (k9_relat_1 @ X12 @ X13) @ 
% 0.24/0.53                 (k9_relat_1 @ X12 @ X14)))
% 0.24/0.53          | ~ (v1_funct_1 @ X12)
% 0.24/0.53          | ~ (v1_relat_1 @ X12))),
% 0.24/0.53      inference('cnf', [status(esa)], [t121_funct_1])).
% 0.24/0.53  thf('8', plain,
% 0.24/0.53      (![X4 : $i, X5 : $i]:
% 0.24/0.53         ((r1_xboole_0 @ X4 @ X5)
% 0.24/0.53          | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.24/0.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.24/0.53  thf('9', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.53         ((r2_hidden @ 
% 0.24/0.53           (sk_C_1 @ (k9_relat_1 @ X2 @ X0) @ (k9_relat_1 @ X2 @ X1)) @ 
% 0.24/0.53           (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.24/0.53          | ~ (v1_relat_1 @ X2)
% 0.24/0.53          | ~ (v1_funct_1 @ X2)
% 0.24/0.53          | ~ (v2_funct_1 @ X2)
% 0.24/0.53          | (r1_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0)))),
% 0.24/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.24/0.53  thf('10', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((r2_hidden @ 
% 0.24/0.53           (sk_C_1 @ (k9_relat_1 @ X0 @ sk_B) @ (k9_relat_1 @ X0 @ sk_A)) @ 
% 0.24/0.53           (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.24/0.53          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.24/0.53          | ~ (v2_funct_1 @ X0)
% 0.24/0.53          | ~ (v1_funct_1 @ X0)
% 0.24/0.53          | ~ (v1_relat_1 @ X0))),
% 0.24/0.53      inference('sup+', [status(thm)], ['6', '9'])).
% 0.24/0.53  thf(t149_relat_1, axiom,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( v1_relat_1 @ A ) =>
% 0.24/0.53       ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.53  thf('11', plain,
% 0.24/0.53      (![X11 : $i]:
% 0.24/0.53         (((k9_relat_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))
% 0.24/0.53          | ~ (v1_relat_1 @ X11))),
% 0.24/0.53      inference('cnf', [status(esa)], [t149_relat_1])).
% 0.24/0.53  thf(t2_boole, axiom,
% 0.24/0.53    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.24/0.53  thf('12', plain,
% 0.24/0.53      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.53      inference('cnf', [status(esa)], [t2_boole])).
% 0.24/0.53  thf('13', plain,
% 0.24/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.24/0.53         (~ (v2_funct_1 @ X12)
% 0.24/0.53          | ((k9_relat_1 @ X12 @ (k3_xboole_0 @ X13 @ X14))
% 0.24/0.53              = (k3_xboole_0 @ (k9_relat_1 @ X12 @ X13) @ 
% 0.24/0.53                 (k9_relat_1 @ X12 @ X14)))
% 0.24/0.53          | ~ (v1_funct_1 @ X12)
% 0.24/0.53          | ~ (v1_relat_1 @ X12))),
% 0.24/0.53      inference('cnf', [status(esa)], [t121_funct_1])).
% 0.24/0.53  thf('14', plain,
% 0.24/0.53      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.24/0.53          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.24/0.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.24/0.53  thf('15', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X3 @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.24/0.53          | ~ (v1_relat_1 @ X2)
% 0.24/0.53          | ~ (v1_funct_1 @ X2)
% 0.24/0.53          | ~ (v2_funct_1 @ X2)
% 0.24/0.53          | ~ (r1_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.24/0.53  thf('16', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X2 @ (k9_relat_1 @ X1 @ k1_xboole_0))
% 0.24/0.53          | ~ (r1_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ 
% 0.24/0.53               (k9_relat_1 @ X1 @ k1_xboole_0))
% 0.24/0.53          | ~ (v2_funct_1 @ X1)
% 0.24/0.53          | ~ (v1_funct_1 @ X1)
% 0.24/0.53          | ~ (v1_relat_1 @ X1))),
% 0.24/0.53      inference('sup-', [status(thm)], ['12', '15'])).
% 0.24/0.53  thf('17', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]:
% 0.24/0.53         (~ (r1_xboole_0 @ k1_xboole_0 @ (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.24/0.53          | ~ (v1_relat_1 @ X0)
% 0.24/0.53          | ~ (v1_relat_1 @ X0)
% 0.24/0.53          | ~ (v1_funct_1 @ X0)
% 0.24/0.53          | ~ (v2_funct_1 @ X0)
% 0.24/0.53          | ~ (r2_hidden @ X1 @ (k9_relat_1 @ X0 @ k1_xboole_0)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['11', '16'])).
% 0.24/0.53  thf('18', plain,
% 0.24/0.53      (![X9 : $i]: ((r1_xboole_0 @ X9 @ X9) | ((X9) != (k1_xboole_0)))),
% 0.24/0.53      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.24/0.53  thf('19', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.24/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.24/0.53  thf('20', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]:
% 0.24/0.53         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.24/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.24/0.53  thf('21', plain,
% 0.24/0.53      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.53      inference('cnf', [status(esa)], [t2_boole])).
% 0.24/0.53  thf('22', plain,
% 0.24/0.53      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.24/0.53          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.24/0.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.24/0.53  thf('23', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.24/0.53  thf('24', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]:
% 0.24/0.53         ((r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X1 @ k1_xboole_0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['20', '23'])).
% 0.24/0.53  thf('25', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.24/0.53      inference('sup-', [status(thm)], ['19', '24'])).
% 0.24/0.53  thf('26', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]:
% 0.24/0.53         (~ (v1_relat_1 @ X0)
% 0.24/0.53          | ~ (v1_relat_1 @ X0)
% 0.24/0.53          | ~ (v1_funct_1 @ X0)
% 0.24/0.53          | ~ (v2_funct_1 @ X0)
% 0.24/0.53          | ~ (r2_hidden @ X1 @ (k9_relat_1 @ X0 @ k1_xboole_0)))),
% 0.24/0.53      inference('demod', [status(thm)], ['17', '25'])).
% 0.24/0.53  thf('27', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X1 @ (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.24/0.53          | ~ (v2_funct_1 @ X0)
% 0.24/0.53          | ~ (v1_funct_1 @ X0)
% 0.24/0.53          | ~ (v1_relat_1 @ X0))),
% 0.24/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.24/0.53  thf('28', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         (~ (v1_relat_1 @ X0)
% 0.24/0.53          | ~ (v1_funct_1 @ X0)
% 0.24/0.53          | ~ (v2_funct_1 @ X0)
% 0.24/0.53          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.24/0.53          | ~ (v1_relat_1 @ X0)
% 0.24/0.53          | ~ (v1_funct_1 @ X0)
% 0.24/0.53          | ~ (v2_funct_1 @ X0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['10', '27'])).
% 0.24/0.53  thf('29', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.24/0.53          | ~ (v2_funct_1 @ X0)
% 0.24/0.53          | ~ (v1_funct_1 @ X0)
% 0.24/0.53          | ~ (v1_relat_1 @ X0))),
% 0.24/0.53      inference('simplify', [status(thm)], ['28'])).
% 0.24/0.53  thf('30', plain,
% 0.24/0.53      (~ (r1_xboole_0 @ (k9_relat_1 @ sk_C_2 @ sk_A) @ 
% 0.24/0.53          (k9_relat_1 @ sk_C_2 @ sk_B))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('31', plain,
% 0.24/0.53      ((~ (v1_relat_1 @ sk_C_2)
% 0.24/0.53        | ~ (v1_funct_1 @ sk_C_2)
% 0.24/0.53        | ~ (v2_funct_1 @ sk_C_2))),
% 0.24/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.24/0.53  thf('32', plain, ((v1_relat_1 @ sk_C_2)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('33', plain, ((v1_funct_1 @ sk_C_2)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('34', plain, ((v2_funct_1 @ sk_C_2)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('35', plain, ($false),
% 0.24/0.53      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.24/0.53  
% 0.24/0.53  % SZS output end Refutation
% 0.24/0.53  
% 0.24/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4ltwiudcmG

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:44 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   42 (  50 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :   16
%              Number of atoms          :  528 ( 622 expanded)
%              Number of equality atoms :   44 (  52 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k1_relat_1 @ X2 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X1: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('4',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_relat_1 @ X2 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X3 ) @ X3 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t63_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k2_funct_1 @ X5 ) )
      | ( ( k5_relat_1 @ X5 @ X4 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) )
      | ( ( k2_relat_1 @ X5 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t65_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v2_funct_1 @ A )
         => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_1])).

thf('19',plain,(
    ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4ltwiudcmG
% 0.14/0.36  % Computer   : n016.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 10:42:04 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 19 iterations in 0.019s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.23/0.49  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.23/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.23/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.23/0.49  thf(t55_funct_1, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.49       ( ( v2_funct_1 @ A ) =>
% 0.23/0.49         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.23/0.49           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.23/0.49  thf('0', plain,
% 0.23/0.50      (![X2 : $i]:
% 0.23/0.50         (~ (v2_funct_1 @ X2)
% 0.23/0.50          | ((k1_relat_1 @ X2) = (k2_relat_1 @ (k2_funct_1 @ X2)))
% 0.23/0.50          | ~ (v1_funct_1 @ X2)
% 0.23/0.50          | ~ (v1_relat_1 @ X2))),
% 0.23/0.50      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.23/0.50  thf(dt_k2_funct_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.50       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.23/0.50         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.23/0.50  thf('1', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0))),
% 0.23/0.50      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.23/0.50  thf('2', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0))),
% 0.23/0.50      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.23/0.50  thf(fc6_funct_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.23/0.50       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.23/0.50         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.23/0.50         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.23/0.50  thf('3', plain,
% 0.23/0.50      (![X1 : $i]:
% 0.23/0.50         ((v2_funct_1 @ (k2_funct_1 @ X1))
% 0.23/0.50          | ~ (v2_funct_1 @ X1)
% 0.23/0.50          | ~ (v1_funct_1 @ X1)
% 0.23/0.50          | ~ (v1_relat_1 @ X1))),
% 0.23/0.50      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.23/0.50  thf('4', plain,
% 0.23/0.50      (![X2 : $i]:
% 0.23/0.50         (~ (v2_funct_1 @ X2)
% 0.23/0.50          | ((k2_relat_1 @ X2) = (k1_relat_1 @ (k2_funct_1 @ X2)))
% 0.23/0.50          | ~ (v1_funct_1 @ X2)
% 0.23/0.50          | ~ (v1_relat_1 @ X2))),
% 0.23/0.50      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.23/0.50  thf(t61_funct_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.50       ( ( v2_funct_1 @ A ) =>
% 0.23/0.50         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.23/0.50             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.23/0.50           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.23/0.50             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.23/0.50  thf('5', plain,
% 0.23/0.50      (![X3 : $i]:
% 0.23/0.50         (~ (v2_funct_1 @ X3)
% 0.23/0.50          | ((k5_relat_1 @ (k2_funct_1 @ X3) @ X3)
% 0.23/0.50              = (k6_relat_1 @ (k2_relat_1 @ X3)))
% 0.23/0.50          | ~ (v1_funct_1 @ X3)
% 0.23/0.50          | ~ (v1_relat_1 @ X3))),
% 0.23/0.50      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.23/0.50  thf(t63_funct_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.50       ( ![B:$i]:
% 0.23/0.50         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.23/0.50           ( ( ( v2_funct_1 @ A ) & 
% 0.23/0.50               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.23/0.50               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.23/0.50             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.23/0.50  thf('6', plain,
% 0.23/0.50      (![X4 : $i, X5 : $i]:
% 0.23/0.50         (~ (v1_relat_1 @ X4)
% 0.23/0.50          | ~ (v1_funct_1 @ X4)
% 0.23/0.50          | ((X4) = (k2_funct_1 @ X5))
% 0.23/0.50          | ((k5_relat_1 @ X5 @ X4) != (k6_relat_1 @ (k1_relat_1 @ X5)))
% 0.23/0.50          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X4))
% 0.23/0.50          | ~ (v2_funct_1 @ X5)
% 0.23/0.50          | ~ (v1_funct_1 @ X5)
% 0.23/0.50          | ~ (v1_relat_1 @ X5))),
% 0.23/0.50      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.23/0.50  thf('7', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((k6_relat_1 @ (k2_relat_1 @ X0))
% 0.23/0.50            != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.23/0.50          | ~ (v1_relat_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.50          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.50          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.50          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.23/0.50          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.50  thf('8', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.23/0.50          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.23/0.50          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.50          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.50          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0)
% 0.23/0.50          | ((k6_relat_1 @ (k2_relat_1 @ X0))
% 0.23/0.50              != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.23/0.50      inference('simplify', [status(thm)], ['7'])).
% 0.23/0.50  thf('9', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((k6_relat_1 @ (k2_relat_1 @ X0)) != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.23/0.50          | ~ (v1_relat_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.50          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.50          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.50          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.23/0.50          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.23/0.50      inference('sup-', [status(thm)], ['4', '8'])).
% 0.23/0.50  thf('10', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.23/0.50          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.23/0.50          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.50          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.50          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0))),
% 0.23/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.23/0.50  thf('11', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (~ (v1_relat_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.50          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.50          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.23/0.50          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.23/0.50      inference('sup-', [status(thm)], ['3', '10'])).
% 0.23/0.50  thf('12', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.23/0.50          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.23/0.50          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.23/0.50          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0))),
% 0.23/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.23/0.50  thf('13', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (~ (v1_relat_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.50          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.23/0.50          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.23/0.50      inference('sup-', [status(thm)], ['2', '12'])).
% 0.23/0.50  thf('14', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.23/0.50          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.23/0.50          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0))),
% 0.23/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.23/0.50  thf('15', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (~ (v1_relat_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.23/0.50          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.23/0.50      inference('sup-', [status(thm)], ['1', '14'])).
% 0.23/0.50  thf('16', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.23/0.50          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0))),
% 0.23/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.23/0.50  thf('17', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.23/0.50          | ~ (v1_relat_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.23/0.50      inference('sup-', [status(thm)], ['0', '16'])).
% 0.23/0.50  thf('18', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0))),
% 0.23/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.23/0.50  thf(t65_funct_1, conjecture,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.50       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i]:
% 0.23/0.50        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.50          ( ( v2_funct_1 @ A ) =>
% 0.23/0.50            ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t65_funct_1])).
% 0.23/0.50  thf('19', plain, (((k2_funct_1 @ (k2_funct_1 @ sk_A)) != (sk_A))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('20', plain,
% 0.23/0.50      ((((sk_A) != (sk_A))
% 0.23/0.50        | ~ (v1_relat_1 @ sk_A)
% 0.23/0.50        | ~ (v1_funct_1 @ sk_A)
% 0.23/0.50        | ~ (v2_funct_1 @ sk_A))),
% 0.23/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.23/0.50  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('22', plain, ((v1_funct_1 @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('23', plain, ((v2_funct_1 @ sk_A)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('24', plain, (((sk_A) != (sk_A))),
% 0.23/0.50      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.23/0.50  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

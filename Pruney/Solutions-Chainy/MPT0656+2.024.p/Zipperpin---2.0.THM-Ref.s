%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0EJBndOFz8

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  76 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :   15
%              Number of atoms          :  595 (1286 expanded)
%              Number of equality atoms :   57 ( 135 expanded)
%              Maximal formula depth    :   21 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('1',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t63_funct_1,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
                = ( k2_funct_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_funct_1])).

thf('2',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X6 ) @ X6 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(l72_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ! [D: $i] :
              ( ( ( v1_relat_1 @ D )
                & ( v1_funct_1 @ D ) )
             => ( ( ( ( k2_relat_1 @ B )
                    = A )
                  & ( ( k5_relat_1 @ B @ C )
                    = ( k6_relat_1 @ ( k1_relat_1 @ D ) ) )
                  & ( ( k5_relat_1 @ C @ D )
                    = ( k6_relat_1 @ A ) ) )
               => ( D = B ) ) ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X3 )
       != X2 )
      | ( ( k5_relat_1 @ X3 @ X1 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ( ( k5_relat_1 @ X1 @ X4 )
       != ( k6_relat_1 @ X2 ) )
      | ( X4 = X3 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l72_funct_1])).

thf('6',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4 = X3 )
      | ( ( k5_relat_1 @ X1 @ X4 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X3 ) ) )
      | ( ( k5_relat_1 @ X3 @ X1 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ X2 @ X1 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X2 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_A ) )
      | ( ( k5_relat_1 @ sk_A @ X0 )
       != ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_A ) )
      | ( ( k5_relat_1 @ sk_A @ X0 )
       != ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11','12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ( ( k5_relat_1 @ sk_A @ X0 )
       != ( k5_relat_1 @ sk_A @ sk_B ) )
      | ( X0
        = ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != ( k5_relat_1 @ sk_A @ sk_B ) )
      | ( X0
        = ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_A ) )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_A ) )
      | ( ( k5_relat_1 @ sk_A @ X0 )
       != ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_A ) )
      | ( ( k5_relat_1 @ sk_A @ X0 )
       != ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24'])).

thf('26',plain,
    ( ( ( k5_relat_1 @ sk_A @ sk_B )
     != ( k5_relat_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference(eq_res,[status(thm)],['25'])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_B
      = ( k2_funct_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( sk_B
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0EJBndOFz8
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:06:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 45 iterations in 0.047s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.50  thf(fc6_funct_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.21/0.50       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.50         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.50         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.50          | ~ (v2_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.50          | ~ (v2_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.21/0.50  thf(t63_funct_1, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50           ( ( ( v2_funct_1 @ A ) & 
% 0.21/0.50               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.21/0.50               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.21/0.50             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50              ( ( ( v2_funct_1 @ A ) & 
% 0.21/0.50                  ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.21/0.50                  ( ( k5_relat_1 @ A @ B ) =
% 0.21/0.50                    ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.21/0.50                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t63_funct_1])).
% 0.21/0.50  thf('2', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t61_funct_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.50       ( ( v2_funct_1 @ A ) =>
% 0.21/0.50         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.21/0.50             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.21/0.50           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.21/0.50             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X6 : $i]:
% 0.21/0.50         (~ (v2_funct_1 @ X6)
% 0.21/0.50          | ((k5_relat_1 @ (k2_funct_1 @ X6) @ X6)
% 0.21/0.50              = (k6_relat_1 @ (k2_relat_1 @ X6)))
% 0.21/0.50          | ~ (v1_funct_1 @ X6)
% 0.21/0.50          | ~ (v1_relat_1 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.21/0.50  thf(t55_funct_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.50       ( ( v2_funct_1 @ A ) =>
% 0.21/0.50         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.21/0.50           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X5 : $i]:
% 0.21/0.50         (~ (v2_funct_1 @ X5)
% 0.21/0.50          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.21/0.50          | ~ (v1_funct_1 @ X5)
% 0.21/0.50          | ~ (v1_relat_1 @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.50  thf(l72_funct_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.50           ( ![D:$i]:
% 0.21/0.50             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 0.21/0.50               ( ( ( ( k2_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.50                   ( ( k5_relat_1 @ B @ C ) =
% 0.21/0.50                     ( k6_relat_1 @ ( k1_relat_1 @ D ) ) ) & 
% 0.21/0.50                   ( ( k5_relat_1 @ C @ D ) = ( k6_relat_1 @ A ) ) ) =>
% 0.21/0.50                 ( ( D ) = ( B ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X1)
% 0.21/0.50          | ~ (v1_funct_1 @ X1)
% 0.21/0.50          | ((k2_relat_1 @ X3) != (X2))
% 0.21/0.50          | ((k5_relat_1 @ X3 @ X1) != (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.21/0.50          | ((k5_relat_1 @ X1 @ X4) != (k6_relat_1 @ X2))
% 0.21/0.50          | ((X4) = (X3))
% 0.21/0.50          | ~ (v1_funct_1 @ X4)
% 0.21/0.50          | ~ (v1_relat_1 @ X4)
% 0.21/0.50          | ~ (v1_funct_1 @ X3)
% 0.21/0.50          | ~ (v1_relat_1 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [l72_funct_1])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X3)
% 0.21/0.50          | ~ (v1_funct_1 @ X3)
% 0.21/0.50          | ~ (v1_relat_1 @ X4)
% 0.21/0.50          | ~ (v1_funct_1 @ X4)
% 0.21/0.50          | ((X4) = (X3))
% 0.21/0.50          | ((k5_relat_1 @ X1 @ X4) != (k6_relat_1 @ (k2_relat_1 @ X3)))
% 0.21/0.50          | ((k5_relat_1 @ X3 @ X1) != (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.21/0.50          | ~ (v1_funct_1 @ X1)
% 0.21/0.50          | ~ (v1_relat_1 @ X1))),
% 0.21/0.50      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (((k5_relat_1 @ X2 @ X1) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v2_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X2)
% 0.21/0.50          | ~ (v1_funct_1 @ X2)
% 0.21/0.50          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X2)
% 0.21/0.50              != (k6_relat_1 @ (k1_relat_1 @ X1)))
% 0.21/0.50          | ((X1) = (k2_funct_1 @ X0))
% 0.21/0.50          | ~ (v1_funct_1 @ X1)
% 0.21/0.50          | ~ (v1_relat_1 @ X1)
% 0.21/0.50          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.50          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k6_relat_1 @ (k2_relat_1 @ X0)) != (k6_relat_1 @ (k1_relat_1 @ X1)))
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v2_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.50          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.50          | ~ (v1_relat_1 @ X1)
% 0.21/0.50          | ~ (v1_funct_1 @ X1)
% 0.21/0.50          | ((X1) = (k2_funct_1 @ X0))
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v2_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ((k5_relat_1 @ X0 @ X1) != (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '7'])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k5_relat_1 @ X0 @ X1) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.21/0.50          | ((X1) = (k2_funct_1 @ X0))
% 0.21/0.50          | ~ (v1_funct_1 @ X1)
% 0.21/0.50          | ~ (v1_relat_1 @ X1)
% 0.21/0.50          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.50          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.50          | ~ (v2_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ((k6_relat_1 @ (k2_relat_1 @ X0))
% 0.21/0.50              != (k6_relat_1 @ (k1_relat_1 @ X1))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k6_relat_1 @ (k1_relat_1 @ sk_B))
% 0.21/0.50            != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.21/0.50          | ~ (v1_relat_1 @ sk_A)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_A)
% 0.21/0.50          | ~ (v2_funct_1 @ sk_A)
% 0.21/0.50          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.21/0.50          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ((X0) = (k2_funct_1 @ sk_A))
% 0.21/0.50          | ((k5_relat_1 @ sk_A @ X0) != (k6_relat_1 @ (k1_relat_1 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '9'])).
% 0.21/0.50  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('12', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('13', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k6_relat_1 @ (k1_relat_1 @ sk_B))
% 0.21/0.50            != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.21/0.50          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.21/0.50          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ((X0) = (k2_funct_1 @ sk_A))
% 0.21/0.50          | ((k5_relat_1 @ sk_A @ X0) != (k5_relat_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['10', '11', '12', '13', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ sk_A)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_A)
% 0.21/0.50          | ~ (v2_funct_1 @ sk_A)
% 0.21/0.50          | ((k5_relat_1 @ sk_A @ X0) != (k5_relat_1 @ sk_A @ sk_B))
% 0.21/0.50          | ((X0) = (k2_funct_1 @ sk_A))
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.21/0.50          | ((k6_relat_1 @ (k1_relat_1 @ sk_B))
% 0.21/0.50              != (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '15'])).
% 0.21/0.50  thf('17', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('18', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('19', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k5_relat_1 @ sk_A @ X0) != (k5_relat_1 @ sk_A @ sk_B))
% 0.21/0.50          | ((X0) = (k2_funct_1 @ sk_A))
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_A))
% 0.21/0.50          | ((k6_relat_1 @ (k1_relat_1 @ sk_B))
% 0.21/0.50              != (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 0.21/0.50      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ sk_A)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_A)
% 0.21/0.50          | ~ (v2_funct_1 @ sk_A)
% 0.21/0.50          | ((k6_relat_1 @ (k1_relat_1 @ sk_B))
% 0.21/0.50              != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ((X0) = (k2_funct_1 @ sk_A))
% 0.21/0.50          | ((k5_relat_1 @ sk_A @ X0) != (k5_relat_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '20'])).
% 0.21/0.50  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('23', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('24', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k6_relat_1 @ (k1_relat_1 @ sk_B))
% 0.21/0.50            != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ((X0) = (k2_funct_1 @ sk_A))
% 0.21/0.50          | ((k5_relat_1 @ sk_A @ X0) != (k5_relat_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      ((((k5_relat_1 @ sk_A @ sk_B) != (k5_relat_1 @ sk_A @ sk_B))
% 0.21/0.50        | ((sk_B) = (k2_funct_1 @ sk_A))
% 0.21/0.50        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.50        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['25'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.50        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.50        | ((sk_B) = (k2_funct_1 @ sk_A)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.50  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('29', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('30', plain, (((sk_B) = (k2_funct_1 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.21/0.50  thf('31', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('32', plain, ($false),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Js3b5iHa0q

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  55 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  395 ( 515 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k8_relat_1 @ X3 @ X2 )
        = ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X7: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf(t85_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_relat_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_relat_1 @ C ) )
         => ( ( B
              = ( k8_relat_1 @ A @ C ) )
          <=> ( ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                 => ( ( k1_funct_1 @ B @ D )
                    = ( k1_funct_1 @ C @ D ) ) )
              & ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                <=> ( ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ A )
                    & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ C ) )
        & ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ A ) ) ) )).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [D: $i,C: $i,B: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
       => ( ( k1_funct_1 @ B @ D )
          = ( k1_funct_1 @ C @ D ) ) ) ) )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( B
              = ( k8_relat_1 @ A @ C ) )
          <=> ( ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                <=> ( zip_tseitin_1 @ D @ C @ A ) )
              & ! [D: $i] :
                  ( zip_tseitin_0 @ D @ C @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X17
       != ( k8_relat_1 @ X18 @ X16 ) )
      | ( zip_tseitin_0 @ X19 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('9',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X18 @ X16 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X18 @ X16 ) )
      | ( zip_tseitin_0 @ X19 @ X16 @ ( k8_relat_1 @ X18 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_0 @ X2 @ X0 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_0 @ X2 @ X0 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X2 @ X0 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t87_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
       => ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
         => ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A )
            = ( k1_funct_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_funct_1])).

thf('14',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( ( k1_funct_1 @ X9 @ X8 )
        = ( k1_funct_1 @ X10 @ X8 ) )
      | ~ ( zip_tseitin_0 @ X8 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ sk_A @ X0 @ ( k8_relat_1 @ sk_B @ sk_C ) )
      | ( ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A )
      = ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,
    ( ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A )
    = ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A )
 != ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('22',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Js3b5iHa0q
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:26:38 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 33 iterations in 0.024s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.21/0.48  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(t123_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i]:
% 0.21/0.48         (((k8_relat_1 @ X3 @ X2) = (k5_relat_1 @ X2 @ (k6_relat_1 @ X3)))
% 0.21/0.48          | ~ (v1_relat_1 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.21/0.48  thf(fc2_funct_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.21/0.48         ( v1_funct_1 @ B ) ) =>
% 0.21/0.48       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.21/0.48         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i]:
% 0.21/0.48         (~ (v1_funct_1 @ X4)
% 0.21/0.48          | ~ (v1_relat_1 @ X4)
% 0.21/0.48          | ~ (v1_relat_1 @ X5)
% 0.21/0.48          | ~ (v1_funct_1 @ X5)
% 0.21/0.48          | (v1_funct_1 @ (k5_relat_1 @ X4 @ X5)))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((v1_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ (k6_relat_1 @ X1))
% 0.21/0.48          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_1 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(fc3_funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.49  thf('3', plain, (![X7 : $i]: (v1_funct_1 @ (k6_relat_1 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf('4', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v1_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (v1_funct_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.49  thf(dt_k8_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v1_relat_1 @ (k8_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.21/0.49  thf(t85_funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.49       ( ![C:$i]:
% 0.21/0.49         ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.21/0.49           ( ( ( B ) = ( k8_relat_1 @ A @ C ) ) <=>
% 0.21/0.49             ( ( ![D:$i]:
% 0.21/0.49                 ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.49                   ( ( k1_funct_1 @ B @ D ) = ( k1_funct_1 @ C @ D ) ) ) ) & 
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) <=>
% 0.21/0.49                   ( ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ A ) & 
% 0.21/0.49                     ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.49  thf(zf_stmt_1, axiom,
% 0.21/0.49    (![D:$i,C:$i,A:$i]:
% 0.21/0.49     ( ( zip_tseitin_1 @ D @ C @ A ) <=>
% 0.21/0.49       ( ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.49         ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ A ) ) ))).
% 0.21/0.49  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.21/0.49  thf(zf_stmt_3, axiom,
% 0.21/0.49    (![D:$i,C:$i,B:$i]:
% 0.21/0.49     ( ( zip_tseitin_0 @ D @ C @ B ) <=>
% 0.21/0.49       ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.49         ( ( k1_funct_1 @ B @ D ) = ( k1_funct_1 @ C @ D ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_4, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.49       ( ![C:$i]:
% 0.21/0.49         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.49           ( ( ( B ) = ( k8_relat_1 @ A @ C ) ) <=>
% 0.21/0.49             ( ( ![D:$i]:
% 0.21/0.49                 ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) <=>
% 0.21/0.49                   ( zip_tseitin_1 @ D @ C @ A ) ) ) & 
% 0.21/0.49               ( ![D:$i]: ( zip_tseitin_0 @ D @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X16)
% 0.21/0.49          | ~ (v1_funct_1 @ X16)
% 0.21/0.49          | ((X17) != (k8_relat_1 @ X18 @ X16))
% 0.21/0.49          | (zip_tseitin_0 @ X19 @ X16 @ X17)
% 0.21/0.49          | ~ (v1_funct_1 @ X17)
% 0.21/0.49          | ~ (v1_relat_1 @ X17))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ (k8_relat_1 @ X18 @ X16))
% 0.21/0.49          | ~ (v1_funct_1 @ (k8_relat_1 @ X18 @ X16))
% 0.21/0.49          | (zip_tseitin_0 @ X19 @ X16 @ (k8_relat_1 @ X18 @ X16))
% 0.21/0.49          | ~ (v1_funct_1 @ X16)
% 0.21/0.49          | ~ (v1_relat_1 @ X16))),
% 0.21/0.49      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | (zip_tseitin_0 @ X2 @ X0 @ (k8_relat_1 @ X1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (v1_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 0.21/0.49          | (zip_tseitin_0 @ X2 @ X0 @ (k8_relat_1 @ X1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | (zip_tseitin_0 @ X2 @ X0 @ (k8_relat_1 @ X1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((zip_tseitin_0 @ X2 @ X0 @ (k8_relat_1 @ X1 @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.49  thf(t87_funct_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.49       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) =>
% 0.21/0.49         ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_5, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.49          ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) =>
% 0.21/0.49            ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A ) =
% 0.21/0.49              ( k1_funct_1 @ C @ A ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t87_funct_1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      ((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X8 @ (k1_relat_1 @ X9))
% 0.21/0.49          | ((k1_funct_1 @ X9 @ X8) = (k1_funct_1 @ X10 @ X8))
% 0.21/0.49          | ~ (zip_tseitin_0 @ X8 @ X10 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (zip_tseitin_0 @ sk_A @ X0 @ (k8_relat_1 @ sk_B @ sk_C))
% 0.21/0.49          | ((k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)
% 0.21/0.49              = (k1_funct_1 @ X0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.49        | ((k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)
% 0.21/0.49            = (k1_funct_1 @ sk_C @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.49  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.49  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (((k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)
% 0.21/0.49         = (k1_funct_1 @ sk_C @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (((k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)
% 0.21/0.49         != (k1_funct_1 @ sk_C @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.49  thf('22', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

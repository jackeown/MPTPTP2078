%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GteGMCCK5T

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 111 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  406 (1025 expanded)
%              Number of equality atoms :   56 ( 122 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t16_funct_1,conjecture,(
    ! [A: $i] :
      ( ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( ( ( k1_relat_1 @ B )
                    = A )
                  & ( ( k1_relat_1 @ C )
                    = A ) )
               => ( B = C ) ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( ( ( k1_relat_1 @ B )
                      = A )
                    & ( ( k1_relat_1 @ C )
                      = A ) )
                 => ( B = C ) ) ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_1])).

thf('0',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(s3_funct_1__e2_24__funct_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ! [D: $i] :
          ( ( r2_hidden @ D @ A )
         => ( ( k1_funct_1 @ C @ D )
            = B ) )
      & ( ( k1_relat_1 @ C )
        = A )
      & ( v1_funct_1 @ C )
      & ( v1_relat_1 @ C ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_relat_1 @ ( sk_C @ X7 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(s3_funct_1__e2_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = k1_xboole_0 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X13 = X12 )
      | ( ( k1_relat_1 @ X12 )
       != sk_A )
      | ( ( k1_relat_1 @ X13 )
       != sk_A )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X10: $i] :
      ( v1_funct_1 @ ( sk_B @ X10 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('6',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( sk_B @ X10 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ ( sk_C @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X1 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( sk_C @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_funct_1 @ ( sk_C @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ( ( sk_C @ X1 @ sk_A )
      = ( sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['18'])).

thf('23',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ X10 ) @ X11 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_B @ X0 ) @ ( sk_D @ X0 @ X1 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ sk_A @ X1 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','26'])).

thf('28',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_funct_1 @ ( sk_C @ X0 @ sk_A ) @ ( sk_D @ sk_A @ X1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('31',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_funct_1 @ ( sk_C @ X7 @ X8 ) @ X9 )
        = X7 )
      | ~ ( r2_hidden @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_C @ X2 @ X0 ) @ ( sk_D @ X0 @ X1 @ k1_xboole_0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] : ( k1_xboole_0 = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GteGMCCK5T
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 57 iterations in 0.038s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(t16_funct_1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ![B:$i]:
% 0.20/0.49         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.49               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.49                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.20/0.49                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.20/0.49       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ![B:$i]:
% 0.20/0.49            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49              ( ![C:$i]:
% 0.20/0.49                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.49                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.49                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.20/0.49                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.20/0.49          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.20/0.49  thf('0', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ?[C:$i]:
% 0.20/0.49       ( ( ![D:$i]:
% 0.20/0.49           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.20/0.49         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.49         ( v1_relat_1 @ C ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]: ((k1_relat_1 @ (sk_C @ X7 @ X8)) = (X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.49  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ?[B:$i]:
% 0.20/0.49       ( ( ![C:$i]:
% 0.20/0.49           ( ( r2_hidden @ C @ A ) =>
% 0.20/0.49             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.49         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.49         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.49  thf('2', plain, (![X10 : $i]: ((k1_relat_1 @ (sk_B @ X10)) = (X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X12)
% 0.20/0.49          | ~ (v1_funct_1 @ X12)
% 0.20/0.49          | ((X13) = (X12))
% 0.20/0.49          | ((k1_relat_1 @ X12) != (sk_A))
% 0.20/0.49          | ((k1_relat_1 @ X13) != (sk_A))
% 0.20/0.49          | ~ (v1_funct_1 @ X13)
% 0.20/0.49          | ~ (v1_relat_1 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((X0) != (sk_A))
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (v1_funct_1 @ X1)
% 0.20/0.49          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.49          | ((X1) = (sk_B @ X0))
% 0.20/0.49          | ~ (v1_funct_1 @ (sk_B @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ (sk_B @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('5', plain, (![X10 : $i]: (v1_funct_1 @ (sk_B @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.49  thf('6', plain, (![X10 : $i]: (v1_relat_1 @ (sk_B @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((X0) != (sk_A))
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (v1_funct_1 @ X1)
% 0.20/0.49          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.49          | ((X1) = (sk_B @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X1 : $i]:
% 0.20/0.49         (((X1) = (sk_B @ sk_A))
% 0.20/0.49          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.49          | ~ (v1_funct_1 @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X1))),
% 0.20/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((X0) != (sk_A))
% 0.20/0.49          | ~ (v1_relat_1 @ (sk_C @ X1 @ X0))
% 0.20/0.49          | ~ (v1_funct_1 @ (sk_C @ X1 @ X0))
% 0.20/0.49          | ((sk_C @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '8'])).
% 0.20/0.49  thf('10', plain, (![X7 : $i, X8 : $i]: (v1_relat_1 @ (sk_C @ X7 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.49  thf('11', plain, (![X7 : $i, X8 : $i]: (v1_funct_1 @ (sk_C @ X7 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((X0) != (sk_A)) | ((sk_C @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.49  thf('13', plain, (![X1 : $i]: ((sk_C @ X1 @ sk_A) = (sk_B @ sk_A))),
% 0.20/0.49      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.49  thf(d5_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.49       ( ![D:$i]:
% 0.20/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.49           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.20/0.49         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.20/0.49          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.20/0.49          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.49  thf(t3_boole, axiom,
% 0.20/0.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.49  thf('15', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.49          | ~ (r2_hidden @ X4 @ X2)
% 0.20/0.49          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X4 @ X2)
% 0.20/0.49          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '17'])).
% 0.20/0.49  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.49      inference('condensation', [status(thm)], ['18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.20/0.49          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.20/0.49          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '19'])).
% 0.20/0.49  thf('22', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.49      inference('condensation', [status(thm)], ['18'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.20/0.49          | ((X1) = (k1_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['20', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]:
% 0.20/0.49         (((k1_funct_1 @ (sk_B @ X10) @ X11) = (k1_xboole_0))
% 0.20/0.49          | ~ (r2_hidden @ X11 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((X0) = (k1_xboole_0))
% 0.20/0.49          | ((k1_funct_1 @ (sk_B @ X0) @ (sk_D @ X0 @ X1 @ k1_xboole_0))
% 0.20/0.49              = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k1_funct_1 @ (sk_C @ X0 @ sk_A) @ (sk_D @ sk_A @ X1 @ k1_xboole_0))
% 0.20/0.49            = (k1_xboole_0))
% 0.20/0.49          | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['13', '26'])).
% 0.20/0.49  thf('28', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k1_funct_1 @ (sk_C @ X0 @ sk_A) @ (sk_D @ sk_A @ X1 @ k1_xboole_0))
% 0.20/0.49           = (k1_xboole_0))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.20/0.49          | ((X1) = (k1_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['20', '23'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         (((k1_funct_1 @ (sk_C @ X7 @ X8) @ X9) = (X7))
% 0.20/0.49          | ~ (r2_hidden @ X9 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (((X0) = (k1_xboole_0))
% 0.20/0.49          | ((k1_funct_1 @ (sk_C @ X2 @ X0) @ (sk_D @ X0 @ X1 @ k1_xboole_0))
% 0.20/0.49              = (X2)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['29', '32'])).
% 0.20/0.49  thf('34', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('35', plain, (![X0 : $i]: ((k1_xboole_0) = (X0))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf('36', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '35'])).
% 0.20/0.49  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

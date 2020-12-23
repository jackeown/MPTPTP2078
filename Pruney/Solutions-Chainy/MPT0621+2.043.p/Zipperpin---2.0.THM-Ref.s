%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j1gb8Myq0W

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 146 expanded)
%              Number of leaves         :   24 (  55 expanded)
%              Depth                    :   19
%              Number of atoms          :  450 (1442 expanded)
%              Number of equality atoms :   75 ( 243 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(np__1_type,type,(
    np__1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(t15_funct_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
        ? [C: $i] :
          ( ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) )
          & ( ( k1_relat_1 @ C )
            = A )
          & ( v1_funct_1 @ C )
          & ( v1_relat_1 @ C ) ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_relat_1 @ ( sk_C @ X16 @ X17 ) )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_funct_1 @ ( sk_C @ X16 @ X17 ) )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ ( sk_C @ X16 @ X17 ) )
        = X17 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(s3_funct_1__e7_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = np__1 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('3',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

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

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X19 = X18 )
      | ( ( k1_relat_1 @ X18 )
       != sk_A )
      | ( ( k1_relat_1 @ X19 )
       != sk_A )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
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
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( sk_B @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('7',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( sk_B @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X1 @ X0 ) )
      | ( ( sk_C @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X1: $i] :
      ( ( ( sk_C @ X1 @ sk_A )
        = ( sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( sk_C @ X1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X1: $i] :
      ( ( ( sk_C @ X1 @ sk_A )
        = ( sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( sk_C @ X1 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C @ X0 @ sk_A ) )
      | ( ( sk_C @ X0 @ sk_A )
        = ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( sk_C @ X0 @ sk_A ) )
      | ( ( sk_C @ X0 @ sk_A )
        = ( sk_B @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( ( sk_C @ X0 @ sk_A )
        = ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf('18',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( sk_C @ X0 @ sk_A )
      = ( sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_relat_1 @ ( sk_C @ X16 @ X17 ) )
        = ( k1_tarski @ X16 ) )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( sk_B @ sk_A ) )
        = ( k1_tarski @ X0 ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( sk_B @ sk_A ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( sk_B @ sk_A ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X0 )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('26',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['25','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['28','37'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] : ( X0 = X1 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] : ( sk_A != X0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j1gb8Myq0W
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:56:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 46 iterations in 0.033s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(np__1_type, type, np__1: $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.50  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.50  thf(t15_funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ?[C:$i]:
% 0.20/0.50           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.20/0.50             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.50             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         ((v1_relat_1 @ (sk_C @ X16 @ X17)) | ((X17) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         ((v1_funct_1 @ (sk_C @ X16 @ X17)) | ((X17) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         (((k1_relat_1 @ (sk_C @ X16 @ X17)) = (X17)) | ((X17) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.50  thf(s3_funct_1__e7_25__funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ?[B:$i]:
% 0.20/0.50       ( ( ![C:$i]:
% 0.20/0.50           ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( np__1 ) ) ) ) & 
% 0.20/0.50         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.50         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.50  thf('3', plain, (![X14 : $i]: ((k1_relat_1 @ (sk_B @ X14)) = (X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.50  thf(t16_funct_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ![B:$i]:
% 0.20/0.50         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.50               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.50                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.20/0.50                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.20/0.50       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ![B:$i]:
% 0.20/0.50            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.50                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.50                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.20/0.50                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.20/0.50          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X18)
% 0.20/0.50          | ~ (v1_funct_1 @ X18)
% 0.20/0.50          | ((X19) = (X18))
% 0.20/0.50          | ((k1_relat_1 @ X18) != (sk_A))
% 0.20/0.50          | ((k1_relat_1 @ X19) != (sk_A))
% 0.20/0.50          | ~ (v1_funct_1 @ X19)
% 0.20/0.50          | ~ (v1_relat_1 @ X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((X0) != (sk_A))
% 0.20/0.50          | ~ (v1_relat_1 @ X1)
% 0.20/0.50          | ~ (v1_funct_1 @ X1)
% 0.20/0.50          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.50          | ((X1) = (sk_B @ X0))
% 0.20/0.50          | ~ (v1_funct_1 @ (sk_B @ X0))
% 0.20/0.50          | ~ (v1_relat_1 @ (sk_B @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf('6', plain, (![X14 : $i]: (v1_funct_1 @ (sk_B @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.50  thf('7', plain, (![X14 : $i]: (v1_relat_1 @ (sk_B @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((X0) != (sk_A))
% 0.20/0.50          | ~ (v1_relat_1 @ X1)
% 0.20/0.50          | ~ (v1_funct_1 @ X1)
% 0.20/0.50          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.50          | ((X1) = (sk_B @ X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X1 : $i]:
% 0.20/0.50         (((X1) = (sk_B @ sk_A))
% 0.20/0.50          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.50          | ~ (v1_funct_1 @ X1)
% 0.20/0.50          | ~ (v1_relat_1 @ X1))),
% 0.20/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((X0) != (sk_A))
% 0.20/0.50          | ((X0) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ (sk_C @ X1 @ X0))
% 0.20/0.50          | ~ (v1_funct_1 @ (sk_C @ X1 @ X0))
% 0.20/0.50          | ((sk_C @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X1 : $i]:
% 0.20/0.50         (((sk_C @ X1 @ sk_A) = (sk_B @ sk_A))
% 0.20/0.50          | ~ (v1_funct_1 @ (sk_C @ X1 @ sk_A))
% 0.20/0.50          | ~ (v1_relat_1 @ (sk_C @ X1 @ sk_A))
% 0.20/0.50          | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.50  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X1 : $i]:
% 0.20/0.50         (((sk_C @ X1 @ sk_A) = (sk_B @ sk_A))
% 0.20/0.50          | ~ (v1_funct_1 @ (sk_C @ X1 @ sk_A))
% 0.20/0.50          | ~ (v1_relat_1 @ (sk_C @ X1 @ sk_A)))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((sk_A) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ (sk_C @ X0 @ sk_A))
% 0.20/0.50          | ((sk_C @ X0 @ sk_A) = (sk_B @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '13'])).
% 0.20/0.50  thf('15', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ (sk_C @ X0 @ sk_A))
% 0.20/0.50          | ((sk_C @ X0 @ sk_A) = (sk_B @ sk_A)))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((sk_A) = (k1_xboole_0)) | ((sk_C @ X0 @ sk_A) = (sk_B @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '16'])).
% 0.20/0.50  thf('18', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('19', plain, (![X0 : $i]: ((sk_C @ X0 @ sk_A) = (sk_B @ sk_A))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         (((k2_relat_1 @ (sk_C @ X16 @ X17)) = (k1_tarski @ X16))
% 0.20/0.50          | ((X17) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k2_relat_1 @ (sk_B @ sk_A)) = (k1_tarski @ X0))
% 0.20/0.50          | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i]: ((k2_relat_1 @ (sk_B @ sk_A)) = (k1_tarski @ X0))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i]: ((k2_relat_1 @ (sk_B @ sk_A)) = (k1_tarski @ X0))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((k1_tarski @ X0) = (k1_tarski @ X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.50  thf(t69_enumset1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.50  thf('26', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.50  thf(t12_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i]:
% 0.20/0.50         ((k1_setfam_1 @ (k2_tarski @ X12 @ X13)) = (k3_xboole_0 @ X12 @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf(t3_boole, axiom,
% 0.20/0.50    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.50  thf('29', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.50  thf(t48_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.20/0.50           = (k3_xboole_0 @ X2 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf(t2_boole, axiom,
% 0.20/0.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.50  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.20/0.50           = (k3_xboole_0 @ X2 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.50  thf('37', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain, (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['28', '37'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['25', '38'])).
% 0.20/0.50  thf('40', plain, (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['28', '37'])).
% 0.20/0.50  thf('41', plain, (![X0 : $i, X1 : $i]: ((X0) = (X1))),
% 0.20/0.50      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('42', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('43', plain, (![X0 : $i]: ((sk_A) != (X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.50  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

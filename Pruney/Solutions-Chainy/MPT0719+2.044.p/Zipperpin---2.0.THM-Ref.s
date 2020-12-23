%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jLpviNgEDO

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 142 expanded)
%              Number of leaves         :   28 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  423 (1081 expanded)
%              Number of equality atoms :   47 ( 151 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t62_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ X7 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t62_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ X11 @ X10 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

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

thf('5',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X8: $i] :
      ( ( ( k1_relat_1 @ X8 )
       != k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( sk_B @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( sk_B @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('12',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4','12'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) )
        = ( k9_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['9'])).

thf('17',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('18',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('19',plain,(
    ! [X9: $i] :
      ( ( ( k1_relat_1 @ X9 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X9 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('20',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('22',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('25',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k11_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','25'])).

thf('27',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('28',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k11_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(d20_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( v5_funct_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
               => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X13 ) @ ( k1_relat_1 @ X12 ) )
      | ( v5_funct_1 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X5 ) )
      | ( ( k11_relat_1 @ X5 @ X6 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v5_funct_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 @ X1 ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 @ X1 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['9'])).

thf('35',plain,(
    ! [X15: $i] :
      ( v1_funct_1 @ ( sk_B @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('36',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t174_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( v5_funct_1 @ k1_xboole_0 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( v5_funct_1 @ k1_xboole_0 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t174_funct_1])).

thf('40',plain,(
    ~ ( v5_funct_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['41','42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jLpviNgEDO
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:45:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 39 iterations in 0.022s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.49  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.49  thf(d16_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((k11_relat_1 @ X0 @ X1) = (k9_relat_1 @ X0 @ (k1_tarski @ X1)))
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.21/0.49  thf(t62_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.49         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X7 : $i]:
% 0.21/0.49         (((k5_relat_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.49          | ~ (v1_relat_1 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t62_relat_1])).
% 0.21/0.49  thf(t94_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         (((k7_relat_1 @ X11 @ X10) = (k5_relat_1 @ (k6_relat_1 @ X10) @ X11))
% 0.21/0.49          | ~ (v1_relat_1 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.21/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.21/0.49  thf('4', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.49  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ?[B:$i]:
% 0.21/0.49       ( ( ![C:$i]:
% 0.21/0.49           ( ( r2_hidden @ C @ A ) =>
% 0.21/0.49             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.49         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.21/0.49         ( v1_relat_1 @ B ) ) ))).
% 0.21/0.49  thf('5', plain, (![X15 : $i]: ((k1_relat_1 @ (sk_B @ X15)) = (X15))),
% 0.21/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.49  thf(t64_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.49           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.49         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X8 : $i]:
% 0.21/0.49         (((k1_relat_1 @ X8) != (k1_xboole_0))
% 0.21/0.49          | ((X8) = (k1_xboole_0))
% 0.21/0.49          | ~ (v1_relat_1 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((X0) != (k1_xboole_0))
% 0.21/0.49          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.21/0.49          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain, (![X15 : $i]: (v1_relat_1 @ (sk_B @ X15))),
% 0.21/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.49  thf('11', plain, (![X15 : $i]: (v1_relat_1 @ (sk_B @ X15))),
% 0.21/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.49  thf('12', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.49      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['3', '4', '12'])).
% 0.21/0.49  thf(t148_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         (((k2_relat_1 @ (k7_relat_1 @ X3 @ X4)) = (k9_relat_1 @ X3 @ X4))
% 0.21/0.49          | ~ (v1_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.49  thf('17', plain, (![X15 : $i]: ((k1_relat_1 @ (sk_B @ X15)) = (X15))),
% 0.21/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.49  thf('18', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf(t65_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.49         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X9 : $i]:
% 0.21/0.49         (((k1_relat_1 @ X9) != (k1_xboole_0))
% 0.21/0.49          | ((k2_relat_1 @ X9) = (k1_xboole_0))
% 0.21/0.49          | ~ (v1_relat_1 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.49        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.49        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('21', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.49      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.49        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.49  thf('24', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.49      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['15', '23', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k1_xboole_0) = (k11_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['0', '25'])).
% 0.21/0.49  thf('27', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.49      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X0 : $i]: ((k1_xboole_0) = (k11_relat_1 @ k1_xboole_0 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf(d20_funct_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.49           ( ( v5_funct_1 @ B @ A ) <=>
% 0.21/0.49             ( ![C:$i]:
% 0.21/0.49               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.49                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X12)
% 0.21/0.49          | ~ (v1_funct_1 @ X12)
% 0.21/0.49          | (r2_hidden @ (sk_C @ X12 @ X13) @ (k1_relat_1 @ X12))
% 0.21/0.49          | (v5_funct_1 @ X12 @ X13)
% 0.21/0.49          | ~ (v1_funct_1 @ X13)
% 0.21/0.49          | ~ (v1_relat_1 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.21/0.49  thf(t205_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.21/0.49         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X6 @ (k1_relat_1 @ X5))
% 0.21/0.49          | ((k11_relat_1 @ X5 @ X6) != (k1_xboole_0))
% 0.21/0.49          | ~ (v1_relat_1 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X1)
% 0.21/0.49          | ~ (v1_funct_1 @ X1)
% 0.21/0.49          | (v5_funct_1 @ X0 @ X1)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ((k11_relat_1 @ X0 @ (sk_C @ X0 @ X1)) != (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((k11_relat_1 @ X0 @ (sk_C @ X0 @ X1)) != (k1_xboole_0))
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | (v5_funct_1 @ X0 @ X1)
% 0.21/0.49          | ~ (v1_funct_1 @ X1)
% 0.21/0.49          | ~ (v1_relat_1 @ X1))),
% 0.21/0.49      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.49          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['28', '32'])).
% 0.21/0.49  thf('34', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.49  thf('35', plain, (![X15 : $i]: (v1_funct_1 @ (sk_B @ X15))),
% 0.21/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.49  thf('36', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.49      inference('sup+', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf('37', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.49      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | (v5_funct_1 @ k1_xboole_0 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['33', '36', '37'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v5_funct_1 @ k1_xboole_0 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.49  thf(t174_funct_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.49       ( v5_funct_1 @ k1_xboole_0 @ A ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.49          ( v5_funct_1 @ k1_xboole_0 @ A ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t174_funct_1])).
% 0.21/0.49  thf('40', plain, (~ (v5_funct_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('41', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_funct_1 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.49  thf('42', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('43', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('44', plain, ($false),
% 0.21/0.49      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

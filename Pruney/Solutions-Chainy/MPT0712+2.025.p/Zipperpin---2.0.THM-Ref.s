%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ubBJuqJtMR

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 152 expanded)
%              Number of leaves         :   27 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  450 (1380 expanded)
%              Number of equality atoms :   32 (  86 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k11_relat_1 @ X10 @ X11 )
        = ( k9_relat_1 @ X10 @ ( k1_tarski @ X11 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t167_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t167_funct_1])).

thf('2',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( r1_tarski @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( r1_tarski @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X3 ) @ X4 )
      | ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_xboole_0 @ X14 @ ( k1_relat_1 @ X15 ) )
      | ( ( k7_relat_1 @ X15 @ X14 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('14',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t142_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) )
    <=> ~ ( ( D != k1_xboole_0 )
          & ( D
           != ( k1_tarski @ A ) )
          & ( D
           != ( k1_tarski @ B ) )
          & ( D
           != ( k1_tarski @ C ) )
          & ( D
           != ( k2_tarski @ A @ B ) )
          & ( D
           != ( k2_tarski @ B @ C ) )
          & ( D
           != ( k2_tarski @ A @ C ) )
          & ( D
           != ( k1_enumset1 @ A @ B @ C ) ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( r1_tarski @ X9 @ ( k1_enumset1 @ X5 @ X6 @ X7 ) )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_enumset1 @ X5 @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['16','22'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( ( k11_relat_1 @ X17 @ X16 )
        = ( k1_tarski @ ( k1_funct_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ~ ( r1_tarski @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k11_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','28'])).

thf('30',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( r1_tarski @ X9 @ ( k1_enumset1 @ X5 @ X6 @ X7 ) )
      | ( X9
       != ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('34',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( r1_tarski @ ( k1_tarski @ X5 ) @ ( k1_enumset1 @ X5 @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','35'])).

thf('37',plain,(
    r1_tarski @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ ( k11_relat_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['30','36'])).

thf('38',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('39',plain,(
    r1_tarski @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k11_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['29','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ubBJuqJtMR
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:17:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 60 iterations in 0.035s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(d16_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         (((k11_relat_1 @ X10 @ X11) = (k9_relat_1 @ X10 @ (k1_tarski @ X11)))
% 0.20/0.48          | ~ (v1_relat_1 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.20/0.48  thf(t148_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.20/0.48          | ~ (v1_relat_1 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.48  thf(t167_funct_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.48       ( r1_tarski @
% 0.20/0.48         ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ 
% 0.20/0.48         ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i]:
% 0.20/0.48        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.48          ( r1_tarski @
% 0.20/0.48            ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ 
% 0.20/0.48            ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t167_funct_1])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (~ (r1_tarski @ 
% 0.20/0.48          (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.20/0.48          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      ((~ (r1_tarski @ (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.20/0.48           (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.20/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (~ (r1_tarski @ (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.20/0.48          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      ((~ (r1_tarski @ (k11_relat_1 @ sk_B @ sk_A) @ 
% 0.20/0.48           (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.20/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '5'])).
% 0.20/0.48  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (~ (r1_tarski @ (k11_relat_1 @ sk_B @ sk_A) @ 
% 0.20/0.48          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf(l27_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ (k1_tarski @ X3) @ X4) | (r2_hidden @ X3 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.48  thf(t187_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.20/0.48           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ X14 @ (k1_relat_1 @ X15))
% 0.20/0.48          | ((k7_relat_1 @ X15 @ X14) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X15))),
% 0.20/0.48      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ((k7_relat_1 @ X0 @ (k1_tarski @ X1)) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (~ (r1_tarski @ 
% 0.20/0.48          (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.20/0.48          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      ((~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ 
% 0.20/0.48           (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.20/0.48        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.48        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf(t60_relat_1, axiom,
% 0.20/0.48    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.48     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf('14', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.48  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.20/0.48        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.20/0.48  thf(t69_enumset1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.48  thf('17', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.48  thf(t70_enumset1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X1 : $i, X2 : $i]:
% 0.20/0.48         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.48  thf(t142_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.48       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.20/0.48            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.20/0.48            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.20/0.48            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.20/0.48            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.20/0.48            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.20/0.48         ((r1_tarski @ X9 @ (k1_enumset1 @ X5 @ X6 @ X7))
% 0.20/0.48          | ((X9) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         (r1_tarski @ k1_xboole_0 @ (k1_enumset1 @ X5 @ X6 @ X7))),
% 0.20/0.48      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['18', '20'])).
% 0.20/0.48  thf('22', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['17', '21'])).
% 0.20/0.48  thf('23', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['16', '22'])).
% 0.20/0.48  thf(t117_funct_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.48       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.48         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X16 : $i, X17 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X16 @ (k1_relat_1 @ X17))
% 0.20/0.48          | ((k11_relat_1 @ X17 @ X16) = (k1_tarski @ (k1_funct_1 @ X17 @ X16)))
% 0.20/0.48          | ~ (v1_funct_1 @ X17)
% 0.20/0.48          | ~ (v1_relat_1 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.48        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.48        | ((k11_relat_1 @ sk_B @ sk_A)
% 0.20/0.48            = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('27', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (~ (r1_tarski @ (k11_relat_1 @ sk_B @ sk_A) @ (k11_relat_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['8', '28'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.48  thf('31', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X1 : $i, X2 : $i]:
% 0.20/0.48         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.20/0.48         ((r1_tarski @ X9 @ (k1_enumset1 @ X5 @ X6 @ X7))
% 0.20/0.48          | ((X9) != (k1_tarski @ X5)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         (r1_tarski @ (k1_tarski @ X5) @ (k1_enumset1 @ X5 @ X6 @ X7))),
% 0.20/0.48      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['32', '34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['31', '35'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      ((r1_tarski @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)) @ 
% 0.20/0.48        (k11_relat_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup+', [status(thm)], ['30', '36'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      ((r1_tarski @ (k11_relat_1 @ sk_B @ sk_A) @ (k11_relat_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.48  thf('40', plain, ($false), inference('demod', [status(thm)], ['29', '39'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

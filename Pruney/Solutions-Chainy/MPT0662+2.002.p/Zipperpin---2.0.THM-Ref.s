%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rzfmTtAp0u

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:46 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   58 (  83 expanded)
%              Number of leaves         :   17 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  512 ( 981 expanded)
%              Number of equality atoms :   16 (  41 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t70_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
         => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
            = ( k1_funct_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_funct_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X9 ) ) )
      | ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X9 ) ) )
      | ( r2_hidden @ X8 @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X14 ) @ X12 )
      | ( X14
       != ( k1_funct_1 @ X12 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ ( k1_funct_1 @ X12 @ X11 ) ) @ X12 )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ sk_C ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(d11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( C
              = ( k7_relat_1 @ A @ B ) )
          <=> ! [D: $i,E: $i] :
                ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
              <=> ( ( r2_hidden @ D @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k7_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('18',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ ( k7_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k7_relat_1 @ sk_C @ X0 ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k7_relat_1 @ sk_C @ X0 ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['4','23'])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('27',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( X14
        = ( k1_funct_1 @ X12 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X14 ) @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k7_relat_1 @ sk_C @ sk_B ) )
      | ( X0
        = ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( X0
        = ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k7_relat_1 @ sk_C @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k7_relat_1 @ sk_C @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k7_relat_1 @ sk_C @ sk_B ) )
      | ( X0
        = ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k7_relat_1 @ sk_C @ sk_B ) )
      | ( X0
        = ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( k1_funct_1 @ sk_C @ sk_A )
    = ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','36'])).

thf('38',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rzfmTtAp0u
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:24:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 153 iterations in 0.223s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.67  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.67  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.67  thf(t70_funct_1, conjecture,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.67       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) =>
% 0.46/0.67         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.67        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.67          ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) =>
% 0.46/0.67            ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 0.46/0.67              ( k1_funct_1 @ C @ A ) ) ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t70_funct_1])).
% 0.46/0.67  thf('0', plain,
% 0.46/0.67      ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(t86_relat_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( v1_relat_1 @ C ) =>
% 0.46/0.67       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.46/0.67         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.46/0.67  thf('1', plain,
% 0.46/0.67      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X8 @ (k1_relat_1 @ (k7_relat_1 @ X10 @ X9)))
% 0.46/0.67          | (r2_hidden @ X8 @ X9)
% 0.46/0.67          | ~ (v1_relat_1 @ X10))),
% 0.46/0.67      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.46/0.67  thf('2', plain, ((~ (v1_relat_1 @ sk_C) | (r2_hidden @ sk_A @ sk_B))),
% 0.46/0.67      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.67  thf('3', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('4', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.46/0.67      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.67  thf('5', plain,
% 0.46/0.67      ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('6', plain,
% 0.46/0.67      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X8 @ (k1_relat_1 @ (k7_relat_1 @ X10 @ X9)))
% 0.46/0.67          | (r2_hidden @ X8 @ (k1_relat_1 @ X10))
% 0.46/0.67          | ~ (v1_relat_1 @ X10))),
% 0.46/0.67      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.46/0.67  thf('7', plain,
% 0.46/0.67      ((~ (v1_relat_1 @ sk_C) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.67  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('9', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.46/0.67      inference('demod', [status(thm)], ['7', '8'])).
% 0.46/0.67  thf(d4_funct_1, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.67       ( ![B:$i,C:$i]:
% 0.46/0.67         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.46/0.67             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.46/0.67               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.67           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.46/0.67             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.46/0.67               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.46/0.67  thf('10', plain,
% 0.46/0.67      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X11 @ (k1_relat_1 @ X12))
% 0.46/0.67          | (r2_hidden @ (k4_tarski @ X11 @ X14) @ X12)
% 0.46/0.67          | ((X14) != (k1_funct_1 @ X12 @ X11))
% 0.46/0.67          | ~ (v1_funct_1 @ X12)
% 0.46/0.67          | ~ (v1_relat_1 @ X12))),
% 0.46/0.67      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.46/0.67  thf('11', plain,
% 0.46/0.67      (![X11 : $i, X12 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X12)
% 0.46/0.67          | ~ (v1_funct_1 @ X12)
% 0.46/0.67          | (r2_hidden @ (k4_tarski @ X11 @ (k1_funct_1 @ X12 @ X11)) @ X12)
% 0.46/0.67          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X12)))),
% 0.46/0.67      inference('simplify', [status(thm)], ['10'])).
% 0.46/0.67  thf('12', plain,
% 0.46/0.67      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ sk_C)
% 0.46/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.67        | ~ (v1_relat_1 @ sk_C))),
% 0.46/0.67      inference('sup-', [status(thm)], ['9', '11'])).
% 0.46/0.67  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('15', plain,
% 0.46/0.67      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ sk_C)),
% 0.46/0.67      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.46/0.67  thf(dt_k7_relat_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.46/0.67  thf('16', plain,
% 0.46/0.67      (![X6 : $i, X7 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X6) | (v1_relat_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.46/0.67      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.46/0.67  thf(d11_relat_1, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( v1_relat_1 @ A ) =>
% 0.46/0.67       ( ![B:$i,C:$i]:
% 0.46/0.67         ( ( v1_relat_1 @ C ) =>
% 0.46/0.67           ( ( ( C ) = ( k7_relat_1 @ A @ B ) ) <=>
% 0.46/0.67             ( ![D:$i,E:$i]:
% 0.46/0.67               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.46/0.67                 ( ( r2_hidden @ D @ B ) & 
% 0.46/0.67                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.46/0.67  thf('17', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X0)
% 0.46/0.67          | ((X0) != (k7_relat_1 @ X1 @ X2))
% 0.46/0.67          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ X0)
% 0.46/0.67          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 0.46/0.67          | ~ (r2_hidden @ X3 @ X2)
% 0.46/0.67          | ~ (v1_relat_1 @ X1))),
% 0.46/0.67      inference('cnf', [status(esa)], [d11_relat_1])).
% 0.46/0.67  thf('18', plain,
% 0.46/0.67      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X1)
% 0.46/0.67          | ~ (r2_hidden @ X3 @ X2)
% 0.46/0.67          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 0.46/0.67          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ (k7_relat_1 @ X1 @ X2))
% 0.46/0.67          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 0.46/0.67      inference('simplify', [status(thm)], ['17'])).
% 0.46/0.67  thf('19', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X1)
% 0.46/0.67          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k7_relat_1 @ X1 @ X0))
% 0.46/0.67          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.46/0.67          | ~ (r2_hidden @ X3 @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['16', '18'])).
% 0.46/0.67  thf('20', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X3 @ X0)
% 0.46/0.67          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.46/0.67          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k7_relat_1 @ X1 @ X0))
% 0.46/0.67          | ~ (v1_relat_1 @ X1))),
% 0.46/0.67      inference('simplify', [status(thm)], ['19'])).
% 0.46/0.67  thf('21', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ sk_C)
% 0.46/0.67          | (r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.46/0.67             (k7_relat_1 @ sk_C @ X0))
% 0.46/0.67          | ~ (r2_hidden @ sk_A @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['15', '20'])).
% 0.46/0.67  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('23', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.46/0.67           (k7_relat_1 @ sk_C @ X0))
% 0.46/0.67          | ~ (r2_hidden @ sk_A @ X0))),
% 0.46/0.67      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.67  thf('24', plain,
% 0.46/0.67      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.46/0.67        (k7_relat_1 @ sk_C @ sk_B))),
% 0.46/0.67      inference('sup-', [status(thm)], ['4', '23'])).
% 0.46/0.67  thf(fc8_funct_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.67       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.46/0.67         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.46/0.67  thf('25', plain,
% 0.46/0.67      (![X15 : $i, X16 : $i]:
% 0.46/0.67         (~ (v1_funct_1 @ X15)
% 0.46/0.67          | ~ (v1_relat_1 @ X15)
% 0.46/0.67          | (v1_funct_1 @ (k7_relat_1 @ X15 @ X16)))),
% 0.46/0.67      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.46/0.67  thf('26', plain,
% 0.46/0.67      (![X6 : $i, X7 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X6) | (v1_relat_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.46/0.67      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.46/0.67  thf('27', plain,
% 0.46/0.67      ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('28', plain,
% 0.46/0.67      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X11 @ (k1_relat_1 @ X12))
% 0.46/0.67          | ((X14) = (k1_funct_1 @ X12 @ X11))
% 0.46/0.67          | ~ (r2_hidden @ (k4_tarski @ X11 @ X14) @ X12)
% 0.46/0.67          | ~ (v1_funct_1 @ X12)
% 0.46/0.67          | ~ (v1_relat_1 @ X12))),
% 0.46/0.67      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.46/0.67  thf('29', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))
% 0.46/0.67          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B))
% 0.46/0.67          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ (k7_relat_1 @ sk_C @ sk_B))
% 0.46/0.67          | ((X0) = (k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.67  thf('30', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ sk_C)
% 0.46/0.67          | ((X0) = (k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A))
% 0.46/0.67          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ (k7_relat_1 @ sk_C @ sk_B))
% 0.46/0.67          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['26', '29'])).
% 0.46/0.67  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('32', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((X0) = (k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A))
% 0.46/0.67          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ (k7_relat_1 @ sk_C @ sk_B))
% 0.46/0.67          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.46/0.67      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.67  thf('33', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ sk_C)
% 0.46/0.67          | ~ (v1_funct_1 @ sk_C)
% 0.46/0.67          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ (k7_relat_1 @ sk_C @ sk_B))
% 0.46/0.67          | ((X0) = (k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['25', '32'])).
% 0.46/0.67  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('36', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ (k7_relat_1 @ sk_C @ sk_B))
% 0.46/0.67          | ((X0) = (k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)))),
% 0.46/0.67      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.46/0.67  thf('37', plain,
% 0.46/0.67      (((k1_funct_1 @ sk_C @ sk_A)
% 0.46/0.67         = (k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['24', '36'])).
% 0.46/0.67  thf('38', plain,
% 0.46/0.67      (((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.46/0.67         != (k1_funct_1 @ sk_C @ sk_A))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('39', plain, ($false),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.46/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

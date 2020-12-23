%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0X77Xiqy58

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 102 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  376 ( 795 expanded)
%              Number of equality atoms :   39 (  77 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t148_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( ( k3_xboole_0 @ B @ C )
          = ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ A ) )
     => ( ( k3_xboole_0 @ A @ C )
        = ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( ( k3_xboole_0 @ B @ C )
            = ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ A ) )
       => ( ( k3_xboole_0 @ A @ C )
          = ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X25: $i,X27: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X25 ) @ X27 )
      | ~ ( r2_hidden @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A )
    = ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k3_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k3_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','25'])).

thf('27',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k3_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('28',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k3_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','24'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','24'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','31'])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['7','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['6','35'])).

thf('37',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C_1 )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('39',plain,(
    ( k3_xboole_0 @ sk_C_1 @ sk_A )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0X77Xiqy58
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:35:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 103 iterations in 0.068s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.53  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(t148_zfmisc_1, conjecture,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( ( r1_tarski @ A @ B ) & 
% 0.22/0.53         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.22/0.53         ( r2_hidden @ D @ A ) ) =>
% 0.22/0.53       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53        ( ( ( r1_tarski @ A @ B ) & 
% 0.22/0.53            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.22/0.53            ( r2_hidden @ D @ A ) ) =>
% 0.22/0.53          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.22/0.53  thf('0', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(l1_zfmisc_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      (![X25 : $i, X27 : $i]:
% 0.22/0.53         ((r1_tarski @ (k1_tarski @ X25) @ X27) | ~ (r2_hidden @ X25 @ X27))),
% 0.22/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.53  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_D_1) @ sk_A)),
% 0.22/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.53  thf(t28_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      (![X15 : $i, X16 : $i]:
% 0.22/0.53         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A) = (k1_tarski @ sk_D_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.53  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)) = (k1_tarski @ sk_D_1))),
% 0.22/0.53      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.53  thf('7', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D_1))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.53  thf('9', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      (![X15 : $i, X16 : $i]:
% 0.22/0.53         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.53  thf('11', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.53  thf('13', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.53  thf(t16_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.53       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.53         ((k3_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14)
% 0.22/0.53           = (k3_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k3_xboole_0 @ sk_A @ X0)
% 0.22/0.53           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['13', '14'])).
% 0.22/0.53  thf('16', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.53  thf(d3_tarski, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.53  thf('17', plain,
% 0.22/0.53      (![X3 : $i, X5 : $i]:
% 0.22/0.53         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      (![X3 : $i, X5 : $i]:
% 0.22/0.53         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.53  thf('19', plain,
% 0.22/0.53      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.53  thf('20', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.22/0.53      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      (![X15 : $i, X16 : $i]:
% 0.22/0.53         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.53  thf('22', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.53         ((k3_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14)
% 0.22/0.53           = (k3_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k3_xboole_0 @ X0 @ X1)
% 0.22/0.53           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k3_xboole_0 @ X0 @ X1)
% 0.22/0.53           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['16', '24'])).
% 0.22/0.53  thf('26', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.22/0.53           = (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ 
% 0.22/0.53              (k3_xboole_0 @ sk_A @ X0)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['15', '25'])).
% 0.22/0.53  thf('27', plain,
% 0.22/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.53         ((k3_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14)
% 0.22/0.53           = (k3_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.22/0.53  thf('28', plain,
% 0.22/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.53         ((k3_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14)
% 0.22/0.53           = (k3_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.22/0.53  thf('29', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k3_xboole_0 @ X0 @ X1)
% 0.22/0.53           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['16', '24'])).
% 0.22/0.53  thf('30', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k3_xboole_0 @ X0 @ X1)
% 0.22/0.53           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['16', '24'])).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B))
% 0.22/0.53           = (k3_xboole_0 @ sk_A @ X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 0.22/0.53  thf('32', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 0.22/0.53           = (k3_xboole_0 @ sk_A @ X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['8', '31'])).
% 0.22/0.53  thf('33', plain,
% 0.22/0.53      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1))
% 0.22/0.53         = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.22/0.53      inference('sup+', [status(thm)], ['7', '32'])).
% 0.22/0.53  thf('34', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.53  thf('35', plain,
% 0.22/0.53      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1))
% 0.22/0.53         = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.22/0.53  thf('36', plain, (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.22/0.53      inference('sup+', [status(thm)], ['6', '35'])).
% 0.22/0.53  thf('37', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) != (k1_tarski @ sk_D_1))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('38', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.53  thf('39', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) != (k1_tarski @ sk_D_1))),
% 0.22/0.53      inference('demod', [status(thm)], ['37', '38'])).
% 0.22/0.53  thf('40', plain, ($false),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['36', '39'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

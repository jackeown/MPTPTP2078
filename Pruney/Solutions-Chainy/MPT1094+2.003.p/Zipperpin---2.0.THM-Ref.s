%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WaZr4pwOCG

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 (  89 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :  341 ( 579 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_funct_3_type,type,(
    k7_funct_3: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_funct_3_type,type,(
    k9_funct_3: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t29_finset_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_finset_1 @ ( k1_relat_1 @ A ) )
      <=> ( v1_finset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_finset_1 @ ( k1_relat_1 @ A ) )
        <=> ( v1_finset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_finset_1])).

thf('0',plain,
    ( ~ ( v1_finset_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_finset_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_finset_1 @ sk_A )
    | ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t26_finset_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_finset_1 @ ( k1_relat_1 @ A ) )
       => ( v1_finset_1 @ ( k2_relat_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X13: $i] :
      ( ~ ( v1_finset_1 @ ( k1_relat_1 @ X13 ) )
      | ( v1_finset_1 @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t26_finset_1])).

thf('5',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( v1_finset_1 @ ( k2_relat_1 @ sk_A ) ) )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v1_finset_1 @ ( k2_relat_1 @ sk_A ) )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(fc14_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_finset_1 @ A )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_finset_1 @ X6 )
      | ~ ( v1_finset_1 @ X7 )
      | ( v1_finset_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[fc14_finset_1])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t13_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ A ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_finset_1 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( v1_finset_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t13_finset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_finset_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ( v1_finset_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_finset_1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_finset_1 @ ( k1_relat_1 @ X0 ) )
      | ( v1_finset_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( v1_finset_1 @ sk_A )
      | ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,
    ( ( v1_finset_1 @ sk_A )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ~ ( v1_finset_1 @ sk_A )
   <= ~ ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ( v1_finset_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_finset_1 @ sk_A )
    | ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('21',plain,
    ( ( v1_finset_1 @ sk_A )
   <= ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(t100_funct_3,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( k9_relat_1 @ ( k9_funct_3 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) @ A )
        = ( k1_relat_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X10: $i] :
      ( ( ( k9_relat_1 @ ( k9_funct_3 @ ( k1_relat_1 @ X10 ) @ ( k2_relat_1 @ X10 ) ) @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t100_funct_3])).

thf(fc13_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ ( k9_relat_1 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_finset_1 @ X5 )
      | ( v1_finset_1 @ ( k9_relat_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc13_finset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_finset_1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_finset_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k9_funct_3 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k9_funct_3 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(dt_k7_funct_3,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_funct_1 @ ( k7_funct_3 @ A @ B ) )
      & ( v1_relat_1 @ ( k7_funct_3 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k7_funct_3 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_funct_3])).

thf(redefinition_k9_funct_3,axiom,(
    ! [A: $i,B: $i] :
      ( ( k9_funct_3 @ A @ B )
      = ( k7_funct_3 @ A @ B ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k9_funct_3 @ X8 @ X9 )
      = ( k7_funct_3 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_funct_3])).

thf('27',plain,(
    ! [X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k9_funct_3 @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( v1_funct_1 @ ( k7_funct_3 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_funct_3])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k9_funct_3 @ X8 @ X9 )
      = ( k7_funct_3 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_funct_3])).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( v1_funct_1 @ ( k9_funct_3 @ X1 @ X3 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_finset_1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_finset_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','27','30'])).

thf('32',plain,
    ( ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( ~ ( v1_finset_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( v1_finset_1 @ sk_A )
   <= ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ~ ( v1_finset_1 @ sk_A )
    | ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','36'])).

thf('38',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','19','20','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WaZr4pwOCG
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:47:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 24 iterations in 0.013s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.46  thf(k7_funct_3_type, type, k7_funct_3: $i > $i > $i).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(k9_funct_3_type, type, k9_funct_3: $i > $i > $i).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.46  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.20/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(t29_finset_1, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.46       ( ( v1_finset_1 @ ( k1_relat_1 @ A ) ) <=> ( v1_finset_1 @ A ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.46          ( ( v1_finset_1 @ ( k1_relat_1 @ A ) ) <=> ( v1_finset_1 @ A ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t29_finset_1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      ((~ (v1_finset_1 @ sk_A) | ~ (v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (~ ((v1_finset_1 @ sk_A)) | ~ ((v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (((v1_finset_1 @ sk_A) | (v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (((v1_finset_1 @ (k1_relat_1 @ sk_A)))
% 0.20/0.46         <= (((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.20/0.46      inference('split', [status(esa)], ['2'])).
% 0.20/0.46  thf(t26_finset_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.46       ( ( v1_finset_1 @ ( k1_relat_1 @ A ) ) =>
% 0.20/0.46         ( v1_finset_1 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X13 : $i]:
% 0.20/0.46         (~ (v1_finset_1 @ (k1_relat_1 @ X13))
% 0.20/0.46          | (v1_finset_1 @ (k2_relat_1 @ X13))
% 0.20/0.46          | ~ (v1_funct_1 @ X13)
% 0.20/0.46          | ~ (v1_relat_1 @ X13))),
% 0.20/0.46      inference('cnf', [status(esa)], [t26_finset_1])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (((~ (v1_relat_1 @ sk_A)
% 0.20/0.46         | ~ (v1_funct_1 @ sk_A)
% 0.20/0.46         | (v1_finset_1 @ (k2_relat_1 @ sk_A))))
% 0.20/0.46         <= (((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.46  thf('6', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('7', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (((v1_finset_1 @ (k2_relat_1 @ sk_A)))
% 0.20/0.46         <= (((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.20/0.46      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.20/0.46  thf(fc14_finset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( v1_finset_1 @ A ) & ( v1_finset_1 @ B ) ) =>
% 0.20/0.46       ( v1_finset_1 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X6 : $i, X7 : $i]:
% 0.20/0.46         (~ (v1_finset_1 @ X6)
% 0.20/0.46          | ~ (v1_finset_1 @ X7)
% 0.20/0.46          | (v1_finset_1 @ (k2_zfmisc_1 @ X6 @ X7)))),
% 0.20/0.46      inference('cnf', [status(esa)], [fc14_finset_1])).
% 0.20/0.46  thf(t21_relat_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ A ) =>
% 0.20/0.46       ( r1_tarski @
% 0.20/0.46         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((r1_tarski @ X0 @ 
% 0.20/0.46           (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.20/0.46          | ~ (v1_relat_1 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.20/0.46  thf(t13_finset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( r1_tarski @ A @ B ) & ( v1_finset_1 @ B ) ) => ( v1_finset_1 @ A ) ))).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X11 : $i, X12 : $i]:
% 0.20/0.46         ((v1_finset_1 @ X11)
% 0.20/0.46          | ~ (r1_tarski @ X11 @ X12)
% 0.20/0.46          | ~ (v1_finset_1 @ X12))),
% 0.20/0.46      inference('cnf', [status(esa)], [t13_finset_1])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X0)
% 0.20/0.46          | ~ (v1_finset_1 @ 
% 0.20/0.46               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.20/0.46          | (v1_finset_1 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (v1_finset_1 @ (k2_relat_1 @ X0))
% 0.20/0.46          | ~ (v1_finset_1 @ (k1_relat_1 @ X0))
% 0.20/0.46          | (v1_finset_1 @ X0)
% 0.20/0.46          | ~ (v1_relat_1 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '12'])).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (((~ (v1_relat_1 @ sk_A)
% 0.20/0.46         | (v1_finset_1 @ sk_A)
% 0.20/0.46         | ~ (v1_finset_1 @ (k1_relat_1 @ sk_A))))
% 0.20/0.46         <= (((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['8', '13'])).
% 0.20/0.46  thf('15', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      (((v1_finset_1 @ (k1_relat_1 @ sk_A)))
% 0.20/0.46         <= (((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.20/0.46      inference('split', [status(esa)], ['2'])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      (((v1_finset_1 @ sk_A)) <= (((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.20/0.46      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.46  thf('18', plain, ((~ (v1_finset_1 @ sk_A)) <= (~ ((v1_finset_1 @ sk_A)))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      (((v1_finset_1 @ sk_A)) | ~ ((v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      (((v1_finset_1 @ sk_A)) | ((v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.20/0.46      inference('split', [status(esa)], ['2'])).
% 0.20/0.46  thf('21', plain, (((v1_finset_1 @ sk_A)) <= (((v1_finset_1 @ sk_A)))),
% 0.20/0.46      inference('split', [status(esa)], ['2'])).
% 0.20/0.46  thf(t100_funct_3, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.46       ( ( k9_relat_1 @
% 0.20/0.46           ( k9_funct_3 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) @ A ) =
% 0.20/0.46         ( k1_relat_1 @ A ) ) ))).
% 0.20/0.46  thf('22', plain,
% 0.20/0.46      (![X10 : $i]:
% 0.20/0.46         (((k9_relat_1 @ 
% 0.20/0.46            (k9_funct_3 @ (k1_relat_1 @ X10) @ (k2_relat_1 @ X10)) @ X10)
% 0.20/0.46            = (k1_relat_1 @ X10))
% 0.20/0.46          | ~ (v1_funct_1 @ X10)
% 0.20/0.46          | ~ (v1_relat_1 @ X10))),
% 0.20/0.46      inference('cnf', [status(esa)], [t100_funct_3])).
% 0.20/0.46  thf(fc13_finset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_finset_1 @ B ) ) =>
% 0.20/0.46       ( v1_finset_1 @ ( k9_relat_1 @ A @ B ) ) ))).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i]:
% 0.20/0.46         (~ (v1_funct_1 @ X4)
% 0.20/0.46          | ~ (v1_relat_1 @ X4)
% 0.20/0.46          | ~ (v1_finset_1 @ X5)
% 0.20/0.46          | (v1_finset_1 @ (k9_relat_1 @ X4 @ X5)))),
% 0.20/0.46      inference('cnf', [status(esa)], [fc13_finset_1])).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((v1_finset_1 @ (k1_relat_1 @ X0))
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | ~ (v1_funct_1 @ X0)
% 0.20/0.46          | ~ (v1_finset_1 @ X0)
% 0.20/0.46          | ~ (v1_relat_1 @ 
% 0.20/0.46               (k9_funct_3 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.20/0.46          | ~ (v1_funct_1 @ 
% 0.20/0.46               (k9_funct_3 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.20/0.46      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.46  thf(dt_k7_funct_3, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_funct_1 @ ( k7_funct_3 @ A @ B ) ) & 
% 0.20/0.46       ( v1_relat_1 @ ( k7_funct_3 @ A @ B ) ) ))).
% 0.20/0.46  thf('25', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i]: (v1_relat_1 @ (k7_funct_3 @ X1 @ X2))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k7_funct_3])).
% 0.20/0.46  thf(redefinition_k9_funct_3, axiom,
% 0.20/0.46    (![A:$i,B:$i]: ( ( k9_funct_3 @ A @ B ) = ( k7_funct_3 @ A @ B ) ))).
% 0.20/0.46  thf('26', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i]: ((k9_funct_3 @ X8 @ X9) = (k7_funct_3 @ X8 @ X9))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k9_funct_3])).
% 0.20/0.46  thf('27', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i]: (v1_relat_1 @ (k9_funct_3 @ X1 @ X2))),
% 0.20/0.46      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.46  thf('28', plain,
% 0.20/0.46      (![X1 : $i, X3 : $i]: (v1_funct_1 @ (k7_funct_3 @ X1 @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k7_funct_3])).
% 0.20/0.46  thf('29', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i]: ((k9_funct_3 @ X8 @ X9) = (k7_funct_3 @ X8 @ X9))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k9_funct_3])).
% 0.20/0.46  thf('30', plain,
% 0.20/0.46      (![X1 : $i, X3 : $i]: (v1_funct_1 @ (k9_funct_3 @ X1 @ X3))),
% 0.20/0.46      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.46  thf('31', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((v1_finset_1 @ (k1_relat_1 @ X0))
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | ~ (v1_funct_1 @ X0)
% 0.20/0.46          | ~ (v1_finset_1 @ X0))),
% 0.20/0.46      inference('demod', [status(thm)], ['24', '27', '30'])).
% 0.20/0.46  thf('32', plain,
% 0.20/0.46      ((~ (v1_finset_1 @ (k1_relat_1 @ sk_A)))
% 0.20/0.46         <= (~ ((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('33', plain,
% 0.20/0.46      (((~ (v1_finset_1 @ sk_A) | ~ (v1_funct_1 @ sk_A) | ~ (v1_relat_1 @ sk_A)))
% 0.20/0.46         <= (~ ((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.46  thf('34', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('35', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('36', plain,
% 0.20/0.46      ((~ (v1_finset_1 @ sk_A)) <= (~ ((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.20/0.46      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.46  thf('37', plain,
% 0.20/0.46      (~ ((v1_finset_1 @ sk_A)) | ((v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['21', '36'])).
% 0.20/0.46  thf('38', plain, ($false),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['1', '19', '20', '37'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

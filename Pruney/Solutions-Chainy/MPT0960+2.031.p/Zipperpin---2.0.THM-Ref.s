%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mm2Phs7urM

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:37 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   50 (  54 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  280 ( 303 expanded)
%              Number of equality atoms :   27 (  29 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t33_wellord2,conjecture,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t33_wellord2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_wellord2 @ sk_A ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X31
       != ( k1_wellord2 @ X30 ) )
      | ( ( k3_relat_1 @ X31 )
        = X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('2',plain,(
    ! [X30: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X30 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X30 ) )
        = X30 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('3',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('4',plain,(
    ! [X30: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X30 ) )
      = X30 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t30_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X29: $i] :
      ( ( ( k2_wellord1 @ X29 @ ( k3_relat_1 @ X29 ) )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t30_wellord1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X0 )
        = ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X0 )
      = ( k1_wellord2 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d6_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k2_wellord1 @ A @ B )
          = ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ B @ B ) ) ) ) )).

thf('9',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_wellord1 @ X27 @ X28 )
        = ( k3_xboole_0 @ X27 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d6_wellord1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
        = ( k5_xboole_0 @ X1 @ ( k2_wellord1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) )
        = ( k5_xboole_0 @ ( k1_wellord2 @ X0 ) @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X34: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mm2Phs7urM
% 0.14/0.37  % Computer   : n001.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 20:59:45 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 51 iterations in 0.028s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.23/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.51  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.23/0.51  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.23/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.51  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.23/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.51  thf(t33_wellord2, conjecture,
% 0.23/0.51    (![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t33_wellord2])).
% 0.23/0.51  thf('0', plain,
% 0.23/0.51      (~ (r1_tarski @ (k1_wellord2 @ sk_A) @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(d1_wellord2, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ B ) =>
% 0.23/0.51       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.23/0.51         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.23/0.51           ( ![C:$i,D:$i]:
% 0.23/0.51             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.23/0.51               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.23/0.51                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.23/0.51  thf('1', plain,
% 0.23/0.51      (![X30 : $i, X31 : $i]:
% 0.23/0.51         (((X31) != (k1_wellord2 @ X30))
% 0.23/0.51          | ((k3_relat_1 @ X31) = (X30))
% 0.23/0.51          | ~ (v1_relat_1 @ X31))),
% 0.23/0.51      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.23/0.51  thf('2', plain,
% 0.23/0.51      (![X30 : $i]:
% 0.23/0.51         (~ (v1_relat_1 @ (k1_wellord2 @ X30))
% 0.23/0.51          | ((k3_relat_1 @ (k1_wellord2 @ X30)) = (X30)))),
% 0.23/0.51      inference('simplify', [status(thm)], ['1'])).
% 0.23/0.51  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.23/0.51  thf('3', plain, (![X34 : $i]: (v1_relat_1 @ (k1_wellord2 @ X34))),
% 0.23/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.23/0.51  thf('4', plain, (![X30 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X30)) = (X30))),
% 0.23/0.51      inference('demod', [status(thm)], ['2', '3'])).
% 0.23/0.51  thf(t30_wellord1, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ A ) =>
% 0.23/0.51       ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) ) = ( A ) ) ))).
% 0.23/0.51  thf('5', plain,
% 0.23/0.51      (![X29 : $i]:
% 0.23/0.51         (((k2_wellord1 @ X29 @ (k3_relat_1 @ X29)) = (X29))
% 0.23/0.51          | ~ (v1_relat_1 @ X29))),
% 0.23/0.51      inference('cnf', [status(esa)], [t30_wellord1])).
% 0.23/0.51  thf('6', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((k2_wellord1 @ (k1_wellord2 @ X0) @ X0) = (k1_wellord2 @ X0))
% 0.23/0.51          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.23/0.51      inference('sup+', [status(thm)], ['4', '5'])).
% 0.23/0.51  thf('7', plain, (![X34 : $i]: (v1_relat_1 @ (k1_wellord2 @ X34))),
% 0.23/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.23/0.51  thf('8', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((k2_wellord1 @ (k1_wellord2 @ X0) @ X0) = (k1_wellord2 @ X0))),
% 0.23/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.23/0.51  thf(d6_wellord1, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ A ) =>
% 0.23/0.51       ( ![B:$i]:
% 0.23/0.51         ( ( k2_wellord1 @ A @ B ) =
% 0.23/0.51           ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ B @ B ) ) ) ) ))).
% 0.23/0.51  thf('9', plain,
% 0.23/0.51      (![X27 : $i, X28 : $i]:
% 0.23/0.51         (((k2_wellord1 @ X27 @ X28)
% 0.23/0.51            = (k3_xboole_0 @ X27 @ (k2_zfmisc_1 @ X28 @ X28)))
% 0.23/0.51          | ~ (v1_relat_1 @ X27))),
% 0.23/0.51      inference('cnf', [status(esa)], [d6_wellord1])).
% 0.23/0.51  thf(t100_xboole_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.23/0.51  thf('10', plain,
% 0.23/0.51      (![X3 : $i, X4 : $i]:
% 0.23/0.51         ((k4_xboole_0 @ X3 @ X4)
% 0.23/0.51           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.23/0.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.23/0.51  thf('11', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (((k4_xboole_0 @ X1 @ (k2_zfmisc_1 @ X0 @ X0))
% 0.23/0.51            = (k5_xboole_0 @ X1 @ (k2_wellord1 @ X1 @ X0)))
% 0.23/0.51          | ~ (v1_relat_1 @ X1))),
% 0.23/0.51      inference('sup+', [status(thm)], ['9', '10'])).
% 0.23/0.51  thf('12', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((k4_xboole_0 @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))
% 0.23/0.51            = (k5_xboole_0 @ (k1_wellord2 @ X0) @ (k1_wellord2 @ X0)))
% 0.23/0.51          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.23/0.51      inference('sup+', [status(thm)], ['8', '11'])).
% 0.23/0.51  thf(t21_xboole_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.23/0.51  thf('13', plain,
% 0.23/0.51      (![X5 : $i, X6 : $i]:
% 0.23/0.51         ((k3_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (X5))),
% 0.23/0.51      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.23/0.51  thf('14', plain,
% 0.23/0.51      (![X3 : $i, X4 : $i]:
% 0.23/0.51         ((k4_xboole_0 @ X3 @ X4)
% 0.23/0.51           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.23/0.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.23/0.51  thf('15', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.23/0.51           = (k5_xboole_0 @ X0 @ X0))),
% 0.23/0.51      inference('sup+', [status(thm)], ['13', '14'])).
% 0.23/0.51  thf(t7_xboole_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.23/0.51  thf('16', plain,
% 0.23/0.51      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 0.23/0.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.23/0.51  thf(l32_xboole_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.23/0.51  thf('17', plain,
% 0.23/0.51      (![X0 : $i, X2 : $i]:
% 0.23/0.51         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.23/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.23/0.51  thf('18', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.51  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.23/0.51      inference('sup+', [status(thm)], ['15', '18'])).
% 0.23/0.51  thf('20', plain, (![X34 : $i]: (v1_relat_1 @ (k1_wellord2 @ X34))),
% 0.23/0.51      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.23/0.51  thf('21', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((k4_xboole_0 @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))
% 0.23/0.51           = (k1_xboole_0))),
% 0.23/0.51      inference('demod', [status(thm)], ['12', '19', '20'])).
% 0.23/0.51  thf('22', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.23/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.23/0.51  thf('23', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((k1_xboole_0) != (k1_xboole_0))
% 0.23/0.51          | (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.23/0.51  thf('24', plain,
% 0.23/0.51      (![X0 : $i]: (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 0.23/0.51      inference('simplify', [status(thm)], ['23'])).
% 0.23/0.51  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

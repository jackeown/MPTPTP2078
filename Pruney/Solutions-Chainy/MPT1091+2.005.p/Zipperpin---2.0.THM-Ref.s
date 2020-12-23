%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ip3e4CdhVA

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 (  90 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  337 ( 635 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t25_finset_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_finset_1 @ A )
        & ! [B: $i] :
            ( ( r2_hidden @ B @ A )
           => ( v1_finset_1 @ B ) ) )
    <=> ( v1_finset_1 @ ( k3_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_finset_1 @ A )
          & ! [B: $i] :
              ( ( r2_hidden @ B @ A )
             => ( v1_finset_1 @ B ) ) )
      <=> ( v1_finset_1 @ ( k3_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_finset_1])).

thf('0',plain,(
    ! [X9: $i] :
      ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ( v1_finset_1 @ X9 )
      | ~ ( r2_hidden @ X9 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X9: $i] :
        ( ( v1_finset_1 @ X9 )
        | ~ ( r2_hidden @ X9 @ sk_A ) )
    | ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ sk_A )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ~ ( v1_finset_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_B_1 )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( v1_finset_1 @ sk_A )
    | ~ ( v1_finset_1 @ sk_B_1 )
    | ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ( v1_finset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ ( k3_tarski @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('10',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k3_tarski @ sk_A ) )
      = sk_B_1 )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc10_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_finset_1 @ B )
     => ( v1_finset_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_finset_1 @ ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( v1_finset_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc10_finset_1])).

thf('14',plain,
    ( ( ( v1_finset_1 @ sk_B_1 )
      | ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v1_finset_1 @ sk_B_1 )
   <= ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      & ( r2_hidden @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,
    ( ~ ( v1_finset_1 @ sk_B_1 )
   <= ~ ( v1_finset_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('17',plain,
    ( ( v1_finset_1 @ sk_B_1 )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['6'])).

thf(fc17_finset_1,axiom,(
    ! [A: $i] :
      ( ( v1_finset_1 @ A )
     => ( v1_finset_1 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X7: $i] :
      ( ( v1_finset_1 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( v1_finset_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc17_finset_1])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('20',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ ( k1_zfmisc_1 @ ( k3_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_finset_1 @ ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( v1_finset_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc10_finset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_finset_1 @ X0 )
      | ~ ( v1_finset_1 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_finset_1 @ ( k3_tarski @ X0 ) )
      | ( v1_finset_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,
    ( ( v1_finset_1 @ sk_A )
   <= ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,
    ( ~ ( v1_finset_1 @ sk_A )
   <= ~ ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('28',plain,
    ( ( v1_finset_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_finset_1 @ sk_A )
    | ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['6'])).

thf('30',plain,
    ( ( v1_finset_1 @ sk_A )
   <= ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf(l22_finset_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_finset_1 @ A )
        & ! [B: $i] :
            ( ( r2_hidden @ B @ A )
           => ( v1_finset_1 @ B ) ) )
     => ( v1_finset_1 @ ( k3_tarski @ A ) ) ) )).

thf('31',plain,(
    ! [X8: $i] :
      ( ( v1_finset_1 @ ( k3_tarski @ X8 ) )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 )
      | ~ ( v1_finset_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l22_finset_1])).

thf('32',plain,
    ( ! [X9: $i] :
        ( ( v1_finset_1 @ X9 )
        | ~ ( r2_hidden @ X9 @ sk_A ) )
   <= ! [X9: $i] :
        ( ( v1_finset_1 @ X9 )
        | ~ ( r2_hidden @ X9 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( ~ ( v1_finset_1 @ sk_A )
      | ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ( v1_finset_1 @ ( sk_B @ sk_A ) ) )
   <= ! [X9: $i] :
        ( ( v1_finset_1 @ X9 )
        | ~ ( r2_hidden @ X9 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X8: $i] :
      ( ( v1_finset_1 @ ( k3_tarski @ X8 ) )
      | ~ ( v1_finset_1 @ ( sk_B @ X8 ) )
      | ~ ( v1_finset_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l22_finset_1])).

thf('35',plain,
    ( ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ~ ( v1_finset_1 @ sk_A ) )
   <= ! [X9: $i] :
        ( ( v1_finset_1 @ X9 )
        | ~ ( r2_hidden @ X9 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ( ( v1_finset_1 @ sk_A )
      & ! [X9: $i] :
          ( ( v1_finset_1 @ X9 )
          | ~ ( r2_hidden @ X9 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('38',plain,
    ( ~ ( v1_finset_1 @ sk_A )
    | ~ ! [X9: $i] :
          ( ( v1_finset_1 @ X9 )
          | ~ ( r2_hidden @ X9 @ sk_A ) )
    | ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','17','28','29','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ip3e4CdhVA
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 38 iterations in 0.016s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.47  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.20/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.47  thf(t25_finset_1, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v1_finset_1 @ A ) & 
% 0.20/0.47         ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v1_finset_1 @ B ) ) ) ) <=>
% 0.20/0.47       ( v1_finset_1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( v1_finset_1 @ A ) & 
% 0.20/0.47            ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v1_finset_1 @ B ) ) ) ) <=>
% 0.20/0.47          ( v1_finset_1 @ ( k3_tarski @ A ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t25_finset_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X9 : $i]:
% 0.20/0.47         ((v1_finset_1 @ (k3_tarski @ sk_A))
% 0.20/0.47          | (v1_finset_1 @ X9)
% 0.20/0.47          | ~ (r2_hidden @ X9 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      ((![X9 : $i]: ((v1_finset_1 @ X9) | ~ (r2_hidden @ X9 @ sk_A))) | 
% 0.20/0.47       ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((~ (v1_finset_1 @ (k3_tarski @ sk_A))
% 0.20/0.47        | (r2_hidden @ sk_B_1 @ sk_A)
% 0.20/0.47        | ~ (v1_finset_1 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (((r2_hidden @ sk_B_1 @ sk_A)) | ~ ((v1_finset_1 @ sk_A)) | 
% 0.20/0.47       ~ ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      ((~ (v1_finset_1 @ (k3_tarski @ sk_A))
% 0.20/0.47        | ~ (v1_finset_1 @ sk_B_1)
% 0.20/0.47        | ~ (v1_finset_1 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (~ ((v1_finset_1 @ sk_A)) | ~ ((v1_finset_1 @ sk_B_1)) | 
% 0.20/0.47       ~ ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.20/0.47      inference('split', [status(esa)], ['4'])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (((v1_finset_1 @ (k3_tarski @ sk_A)) | (v1_finset_1 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (((v1_finset_1 @ (k3_tarski @ sk_A)))
% 0.20/0.47         <= (((v1_finset_1 @ (k3_tarski @ sk_A))))),
% 0.20/0.47      inference('split', [status(esa)], ['6'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (((r2_hidden @ sk_B_1 @ sk_A)) <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf(l49_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i]:
% 0.20/0.47         ((r1_tarski @ X2 @ (k3_tarski @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (((r1_tarski @ sk_B_1 @ (k3_tarski @ sk_A)))
% 0.20/0.47         <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf(t28_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      ((((k3_xboole_0 @ sk_B_1 @ (k3_tarski @ sk_A)) = (sk_B_1)))
% 0.20/0.47         <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf(fc10_finset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_finset_1 @ B ) => ( v1_finset_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i]:
% 0.20/0.47         ((v1_finset_1 @ (k3_xboole_0 @ X5 @ X6)) | ~ (v1_finset_1 @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc10_finset_1])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      ((((v1_finset_1 @ sk_B_1) | ~ (v1_finset_1 @ (k3_tarski @ sk_A))))
% 0.20/0.47         <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (((v1_finset_1 @ sk_B_1))
% 0.20/0.47         <= (((v1_finset_1 @ (k3_tarski @ sk_A))) & 
% 0.20/0.47             ((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['7', '14'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      ((~ (v1_finset_1 @ sk_B_1)) <= (~ ((v1_finset_1 @ sk_B_1)))),
% 0.20/0.47      inference('split', [status(esa)], ['4'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (((v1_finset_1 @ sk_B_1)) | ~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 0.20/0.47       ~ ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (((v1_finset_1 @ (k3_tarski @ sk_A)))
% 0.20/0.47         <= (((v1_finset_1 @ (k3_tarski @ sk_A))))),
% 0.20/0.47      inference('split', [status(esa)], ['6'])).
% 0.20/0.47  thf(fc17_finset_1, axiom,
% 0.20/0.47    (![A:$i]: ( ( v1_finset_1 @ A ) => ( v1_finset_1 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X7 : $i]: ((v1_finset_1 @ (k1_zfmisc_1 @ X7)) | ~ (v1_finset_1 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc17_finset_1])).
% 0.20/0.47  thf(t100_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X4 : $i]: (r1_tarski @ X4 @ (k1_zfmisc_1 @ (k3_tarski @ X4)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k3_xboole_0 @ X0 @ (k1_zfmisc_1 @ (k3_tarski @ X0))) = (X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i]:
% 0.20/0.47         ((v1_finset_1 @ (k3_xboole_0 @ X5 @ X6)) | ~ (v1_finset_1 @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc10_finset_1])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v1_finset_1 @ X0)
% 0.20/0.47          | ~ (v1_finset_1 @ (k1_zfmisc_1 @ (k3_tarski @ X0))))),
% 0.20/0.47      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X0 : $i]: (~ (v1_finset_1 @ (k3_tarski @ X0)) | (v1_finset_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['19', '24'])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (((v1_finset_1 @ sk_A)) <= (((v1_finset_1 @ (k3_tarski @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['18', '25'])).
% 0.20/0.47  thf('27', plain, ((~ (v1_finset_1 @ sk_A)) <= (~ ((v1_finset_1 @ sk_A)))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (((v1_finset_1 @ sk_A)) | ~ ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      (((v1_finset_1 @ sk_A)) | ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.20/0.47      inference('split', [status(esa)], ['6'])).
% 0.20/0.47  thf('30', plain, (((v1_finset_1 @ sk_A)) <= (((v1_finset_1 @ sk_A)))),
% 0.20/0.47      inference('split', [status(esa)], ['6'])).
% 0.20/0.47  thf(l22_finset_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v1_finset_1 @ A ) & 
% 0.20/0.47         ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v1_finset_1 @ B ) ) ) ) =>
% 0.20/0.47       ( v1_finset_1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (![X8 : $i]:
% 0.20/0.47         ((v1_finset_1 @ (k3_tarski @ X8))
% 0.20/0.47          | (r2_hidden @ (sk_B @ X8) @ X8)
% 0.20/0.47          | ~ (v1_finset_1 @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [l22_finset_1])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      ((![X9 : $i]: ((v1_finset_1 @ X9) | ~ (r2_hidden @ X9 @ sk_A)))
% 0.20/0.47         <= ((![X9 : $i]: ((v1_finset_1 @ X9) | ~ (r2_hidden @ X9 @ sk_A))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      (((~ (v1_finset_1 @ sk_A)
% 0.20/0.47         | (v1_finset_1 @ (k3_tarski @ sk_A))
% 0.20/0.47         | (v1_finset_1 @ (sk_B @ sk_A))))
% 0.20/0.47         <= ((![X9 : $i]: ((v1_finset_1 @ X9) | ~ (r2_hidden @ X9 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      (![X8 : $i]:
% 0.20/0.47         ((v1_finset_1 @ (k3_tarski @ X8))
% 0.20/0.47          | ~ (v1_finset_1 @ (sk_B @ X8))
% 0.20/0.47          | ~ (v1_finset_1 @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [l22_finset_1])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      ((((v1_finset_1 @ (k3_tarski @ sk_A)) | ~ (v1_finset_1 @ sk_A)))
% 0.20/0.47         <= ((![X9 : $i]: ((v1_finset_1 @ X9) | ~ (r2_hidden @ X9 @ sk_A))))),
% 0.20/0.47      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      (((v1_finset_1 @ (k3_tarski @ sk_A)))
% 0.20/0.47         <= (((v1_finset_1 @ sk_A)) & 
% 0.20/0.47             (![X9 : $i]: ((v1_finset_1 @ X9) | ~ (r2_hidden @ X9 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['30', '35'])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      ((~ (v1_finset_1 @ (k3_tarski @ sk_A)))
% 0.20/0.47         <= (~ ((v1_finset_1 @ (k3_tarski @ sk_A))))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      (~ ((v1_finset_1 @ sk_A)) | 
% 0.20/0.47       ~ (![X9 : $i]: ((v1_finset_1 @ X9) | ~ (r2_hidden @ X9 @ sk_A))) | 
% 0.20/0.47       ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.47  thf('39', plain, ($false),
% 0.20/0.47      inference('sat_resolution*', [status(thm)],
% 0.20/0.47                ['1', '3', '5', '17', '28', '29', '38'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

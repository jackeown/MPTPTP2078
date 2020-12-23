%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jE0tMdF3j0

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 (  91 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  347 ( 647 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf('0',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ( v1_finset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v1_finset_1 @ sk_A )
   <= ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(l22_finset_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_finset_1 @ A )
        & ! [B: $i] :
            ( ( r2_hidden @ B @ A )
           => ( v1_finset_1 @ B ) ) )
     => ( v1_finset_1 @ ( k3_tarski @ A ) ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( v1_finset_1 @ ( k3_tarski @ X9 ) )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 )
      | ~ ( v1_finset_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l22_finset_1])).

thf('3',plain,(
    ! [X12: $i] :
      ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ( v1_finset_1 @ X12 )
      | ~ ( r2_hidden @ X12 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ! [X12: $i] :
        ( ( v1_finset_1 @ X12 )
        | ~ ( r2_hidden @ X12 @ sk_A ) )
   <= ! [X12: $i] :
        ( ( v1_finset_1 @ X12 )
        | ~ ( r2_hidden @ X12 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ~ ( v1_finset_1 @ sk_A )
      | ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ( v1_finset_1 @ ( sk_B @ sk_A ) ) )
   <= ! [X12: $i] :
        ( ( v1_finset_1 @ X12 )
        | ~ ( r2_hidden @ X12 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X9: $i] :
      ( ( v1_finset_1 @ ( k3_tarski @ X9 ) )
      | ~ ( v1_finset_1 @ ( sk_B @ X9 ) )
      | ~ ( v1_finset_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l22_finset_1])).

thf('7',plain,
    ( ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ~ ( v1_finset_1 @ sk_A ) )
   <= ! [X12: $i] :
        ( ( v1_finset_1 @ X12 )
        | ~ ( r2_hidden @ X12 @ sk_A ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ( ( v1_finset_1 @ sk_A )
      & ! [X12: $i] :
          ( ( v1_finset_1 @ X12 )
          | ~ ( r2_hidden @ X12 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ sk_A )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ~ ! [X12: $i] :
          ( ( v1_finset_1 @ X12 )
          | ~ ( r2_hidden @ X12 @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_A )
    | ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_B_1 )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_B_1 )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('15',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
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

thf(t56_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
        & ( r2_hidden @ C @ A ) )
     => ( r1_tarski @ C @ B ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ X5 ) @ X6 )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t56_setfam_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k3_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf(t13_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ A ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_finset_1 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( v1_finset_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t13_finset_1])).

thf('25',plain,
    ( ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ( v1_finset_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_finset_1 @ sk_B_1 )
   <= ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      & ( r2_hidden @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','25'])).

thf('27',plain,
    ( ~ ( v1_finset_1 @ sk_B_1 )
   <= ~ ( v1_finset_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['12'])).

thf('28',plain,
    ( ( v1_finset_1 @ sk_B_1 )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ! [X12: $i] :
        ( ( v1_finset_1 @ X12 )
        | ~ ( r2_hidden @ X12 @ sk_A ) )
    | ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(fc17_finset_1,axiom,(
    ! [A: $i] :
      ( ( v1_finset_1 @ A )
     => ( v1_finset_1 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X8: $i] :
      ( ( v1_finset_1 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( v1_finset_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc17_finset_1])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('33',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ ( k1_zfmisc_1 @ ( k3_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_finset_1 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( v1_finset_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t13_finset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_finset_1 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) )
      | ( v1_finset_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_finset_1 @ ( k3_tarski @ X0 ) )
      | ( v1_finset_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ( v1_finset_1 @ sk_A )
   <= ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,
    ( ~ ( v1_finset_1 @ sk_A )
   <= ~ ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('39',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['11','13','14','28','29','30','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jE0tMdF3j0
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:07:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 61 iterations in 0.031s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.48  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(t25_finset_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v1_finset_1 @ A ) & 
% 0.20/0.48         ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v1_finset_1 @ B ) ) ) ) <=>
% 0.20/0.48       ( v1_finset_1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( v1_finset_1 @ A ) & 
% 0.20/0.48            ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v1_finset_1 @ B ) ) ) ) <=>
% 0.20/0.48          ( v1_finset_1 @ ( k3_tarski @ A ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t25_finset_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (((v1_finset_1 @ (k3_tarski @ sk_A)) | (v1_finset_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain, (((v1_finset_1 @ sk_A)) <= (((v1_finset_1 @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf(l22_finset_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v1_finset_1 @ A ) & 
% 0.20/0.48         ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v1_finset_1 @ B ) ) ) ) =>
% 0.20/0.48       ( v1_finset_1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X9 : $i]:
% 0.20/0.48         ((v1_finset_1 @ (k3_tarski @ X9))
% 0.20/0.48          | (r2_hidden @ (sk_B @ X9) @ X9)
% 0.20/0.48          | ~ (v1_finset_1 @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [l22_finset_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X12 : $i]:
% 0.20/0.48         ((v1_finset_1 @ (k3_tarski @ sk_A))
% 0.20/0.48          | (v1_finset_1 @ X12)
% 0.20/0.48          | ~ (r2_hidden @ X12 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      ((![X12 : $i]: ((v1_finset_1 @ X12) | ~ (r2_hidden @ X12 @ sk_A)))
% 0.20/0.48         <= ((![X12 : $i]: ((v1_finset_1 @ X12) | ~ (r2_hidden @ X12 @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (((~ (v1_finset_1 @ sk_A)
% 0.20/0.48         | (v1_finset_1 @ (k3_tarski @ sk_A))
% 0.20/0.48         | (v1_finset_1 @ (sk_B @ sk_A))))
% 0.20/0.48         <= ((![X12 : $i]: ((v1_finset_1 @ X12) | ~ (r2_hidden @ X12 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '4'])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X9 : $i]:
% 0.20/0.48         ((v1_finset_1 @ (k3_tarski @ X9))
% 0.20/0.48          | ~ (v1_finset_1 @ (sk_B @ X9))
% 0.20/0.48          | ~ (v1_finset_1 @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [l22_finset_1])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      ((((v1_finset_1 @ (k3_tarski @ sk_A)) | ~ (v1_finset_1 @ sk_A)))
% 0.20/0.48         <= ((![X12 : $i]: ((v1_finset_1 @ X12) | ~ (r2_hidden @ X12 @ sk_A))))),
% 0.20/0.48      inference('clc', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (((v1_finset_1 @ (k3_tarski @ sk_A)))
% 0.20/0.48         <= (((v1_finset_1 @ sk_A)) & 
% 0.20/0.48             (![X12 : $i]: ((v1_finset_1 @ X12) | ~ (r2_hidden @ X12 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      ((~ (v1_finset_1 @ (k3_tarski @ sk_A))
% 0.20/0.48        | (r2_hidden @ sk_B_1 @ sk_A)
% 0.20/0.48        | ~ (v1_finset_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((~ (v1_finset_1 @ (k3_tarski @ sk_A)))
% 0.20/0.48         <= (~ ((v1_finset_1 @ (k3_tarski @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (~ (![X12 : $i]: ((v1_finset_1 @ X12) | ~ (r2_hidden @ X12 @ sk_A))) | 
% 0.20/0.48       ~ ((v1_finset_1 @ sk_A)) | ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      ((~ (v1_finset_1 @ (k3_tarski @ sk_A))
% 0.20/0.48        | ~ (v1_finset_1 @ sk_B_1)
% 0.20/0.48        | ~ (v1_finset_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (~ ((v1_finset_1 @ (k3_tarski @ sk_A))) | ~ ((v1_finset_1 @ sk_B_1)) | 
% 0.20/0.48       ~ ((v1_finset_1 @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (((r2_hidden @ sk_B_1 @ sk_A)) | 
% 0.20/0.48       ~ ((v1_finset_1 @ (k3_tarski @ sk_A))) | ~ ((v1_finset_1 @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['9'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (((v1_finset_1 @ (k3_tarski @ sk_A)))
% 0.20/0.48         <= (((v1_finset_1 @ (k3_tarski @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (((r2_hidden @ sk_B_1 @ sk_A)) <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['9'])).
% 0.20/0.48  thf(d3_tarski, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X1 : $i, X3 : $i]:
% 0.20/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X1 : $i, X3 : $i]:
% 0.20/0.48         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.48      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.48  thf(t56_setfam_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 0.20/0.48       ( r1_tarski @ C @ B ) ))).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k3_tarski @ X5) @ X6)
% 0.20/0.48          | ~ (r2_hidden @ X7 @ X5)
% 0.20/0.48          | (r1_tarski @ X7 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [t56_setfam_1])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r1_tarski @ X1 @ (k3_tarski @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (((r1_tarski @ sk_B_1 @ (k3_tarski @ sk_A)))
% 0.20/0.48         <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '22'])).
% 0.20/0.48  thf(t13_finset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( r1_tarski @ A @ B ) & ( v1_finset_1 @ B ) ) => ( v1_finset_1 @ A ) ))).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         ((v1_finset_1 @ X10)
% 0.20/0.48          | ~ (r1_tarski @ X10 @ X11)
% 0.20/0.48          | ~ (v1_finset_1 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [t13_finset_1])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (((~ (v1_finset_1 @ (k3_tarski @ sk_A)) | (v1_finset_1 @ sk_B_1)))
% 0.20/0.48         <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (((v1_finset_1 @ sk_B_1))
% 0.20/0.48         <= (((v1_finset_1 @ (k3_tarski @ sk_A))) & 
% 0.20/0.48             ((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '25'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      ((~ (v1_finset_1 @ sk_B_1)) <= (~ ((v1_finset_1 @ sk_B_1)))),
% 0.20/0.48      inference('split', [status(esa)], ['12'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (((v1_finset_1 @ sk_B_1)) | ~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 0.20/0.48       ~ ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      ((![X12 : $i]: ((v1_finset_1 @ X12) | ~ (r2_hidden @ X12 @ sk_A))) | 
% 0.20/0.48       ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (((v1_finset_1 @ (k3_tarski @ sk_A))) | ((v1_finset_1 @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (((v1_finset_1 @ (k3_tarski @ sk_A)))
% 0.20/0.48         <= (((v1_finset_1 @ (k3_tarski @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf(fc17_finset_1, axiom,
% 0.20/0.48    (![A:$i]: ( ( v1_finset_1 @ A ) => ( v1_finset_1 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X8 : $i]: ((v1_finset_1 @ (k1_zfmisc_1 @ X8)) | ~ (v1_finset_1 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc17_finset_1])).
% 0.20/0.48  thf(t100_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X4 : $i]: (r1_tarski @ X4 @ (k1_zfmisc_1 @ (k3_tarski @ X4)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         ((v1_finset_1 @ X10)
% 0.20/0.48          | ~ (r1_tarski @ X10 @ X11)
% 0.20/0.48          | ~ (v1_finset_1 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [t13_finset_1])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_finset_1 @ (k1_zfmisc_1 @ (k3_tarski @ X0)))
% 0.20/0.48          | (v1_finset_1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (![X0 : $i]: (~ (v1_finset_1 @ (k3_tarski @ X0)) | (v1_finset_1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['32', '35'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (((v1_finset_1 @ sk_A)) <= (((v1_finset_1 @ (k3_tarski @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['31', '36'])).
% 0.20/0.48  thf('38', plain, ((~ (v1_finset_1 @ sk_A)) <= (~ ((v1_finset_1 @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['9'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (~ ((v1_finset_1 @ (k3_tarski @ sk_A))) | ((v1_finset_1 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.48  thf('40', plain, ($false),
% 0.20/0.48      inference('sat_resolution*', [status(thm)],
% 0.20/0.48                ['11', '13', '14', '28', '29', '30', '39'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

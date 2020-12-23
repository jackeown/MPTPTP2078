%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ypGFqMhyrF

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 (  99 expanded)
%              Number of leaves         :   23 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  469 ( 737 expanded)
%              Number of equality atoms :   30 (  53 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v3_relat_1_type,type,(
    v3_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t184_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v3_relat_1 @ A )
      <=> ! [B: $i] :
            ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) )
           => ( B = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( v3_relat_1 @ A )
        <=> ! [B: $i] :
              ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) )
             => ( B = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t184_relat_1])).

thf('0',plain,
    ( ( sk_B != k1_xboole_0 )
    | ~ ( v3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B != k1_xboole_0 )
    | ~ ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X32: $i] :
      ( ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ sk_A ) )
      | ( X32 = k1_xboole_0 )
      | ( v3_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v3_relat_1 @ sk_A )
   <= ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d15_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v3_relat_1 @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_tarski @ k1_xboole_0 ) ) ) ) )).

thf('7',plain,(
    ! [X31: $i] :
      ( ~ ( v3_relat_1 @ X31 )
      | ( r1_tarski @ ( k2_relat_1 @ X31 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d15_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v3_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( v3_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( v3_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
   <= ( ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X26: $i,X27: $i] :
      ( ( m1_subset_1 @ X26 @ X27 )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('15',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
   <= ( ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('16',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) )
      | ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ sk_B @ k1_xboole_0 )
   <= ( ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('20',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v3_relat_1 @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ sk_A ) ) )
    | ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ ( k2_tarski @ X22 @ X24 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,
    ( ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) )
          = k1_xboole_0 ) )
   <= ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ k1_xboole_0 @ X0 )
        | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) )
   <= ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ k1_xboole_0 @ X0 ) )
   <= ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_tarski @ k1_xboole_0 ) )
   <= ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    ! [X31: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ( v3_relat_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d15_relat_1])).

thf('42',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( v3_relat_1 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v3_relat_1 @ sk_A )
   <= ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v3_relat_1 @ sk_A )
   <= ~ ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,
    ( ~ ! [X32: $i] :
          ( ( X32 = k1_xboole_0 )
          | ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ sk_A ) ) )
    | ( v3_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','26','27','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ypGFqMhyrF
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:18:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 140 iterations in 0.080s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.54  thf(v3_relat_1_type, type, v3_relat_1: $i > $o).
% 0.21/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.54  thf(t184_relat_1, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ( v3_relat_1 @ A ) <=>
% 0.21/0.54         ( ![B:$i]:
% 0.21/0.54           ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) ) =>
% 0.21/0.54             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( v1_relat_1 @ A ) =>
% 0.21/0.54          ( ( v3_relat_1 @ A ) <=>
% 0.21/0.54            ( ![B:$i]:
% 0.21/0.54              ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) ) =>
% 0.21/0.54                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t184_relat_1])).
% 0.21/0.54  thf('0', plain, ((((sk_B) != (k1_xboole_0)) | ~ (v3_relat_1 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain, (~ (((sk_B) = (k1_xboole_0))) | ~ ((v3_relat_1 @ sk_A))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A)) | ~ (v3_relat_1 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))) | ~ ((v3_relat_1 @ sk_A))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (![X32 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A))
% 0.21/0.54          | ((X32) = (k1_xboole_0))
% 0.21/0.54          | (v3_relat_1 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('5', plain, (((v3_relat_1 @ sk_A)) <= (((v3_relat_1 @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['4'])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.21/0.54         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf(d15_relat_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ( v3_relat_1 @ A ) <=>
% 0.21/0.54         ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_tarski @ k1_xboole_0 ) ) ) ))).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X31 : $i]:
% 0.21/0.54         (~ (v3_relat_1 @ X31)
% 0.21/0.54          | (r1_tarski @ (k2_relat_1 @ X31) @ (k1_tarski @ k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X31))),
% 0.21/0.54      inference('cnf', [status(esa)], [d15_relat_1])).
% 0.21/0.54  thf(d3_tarski, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.54          | (r2_hidden @ X0 @ X2)
% 0.21/0.54          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v3_relat_1 @ X0)
% 0.21/0.54          | (r2_hidden @ X1 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.54          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      ((((r2_hidden @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.21/0.54         | ~ (v3_relat_1 @ sk_A)
% 0.21/0.54         | ~ (v1_relat_1 @ sk_A)))
% 0.21/0.54         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.54  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      ((((r2_hidden @ sk_B @ (k1_tarski @ k1_xboole_0)) | ~ (v3_relat_1 @ sk_A)))
% 0.21/0.54         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ (k1_tarski @ k1_xboole_0)))
% 0.21/0.54         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '12'])).
% 0.21/0.54  thf(t1_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X26 : $i, X27 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X26 @ X27) | ~ (r2_hidden @ X26 @ X27))),
% 0.21/0.54      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (((m1_subset_1 @ sk_B @ (k1_tarski @ k1_xboole_0)))
% 0.21/0.54         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.54  thf(t1_zfmisc_1, axiom,
% 0.21/0.54    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.21/0.54  thf('16', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.21/0.54  thf(t3_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X28 : $i, X29 : $i]:
% 0.21/0.54         ((r1_tarski @ X28 @ X29) | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.54          | (r1_tarski @ X0 @ k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (((r1_tarski @ sk_B @ k1_xboole_0))
% 0.21/0.54         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['15', '18'])).
% 0.21/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.54  thf('20', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.54  thf(d10_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (![X4 : $i, X6 : $i]:
% 0.21/0.54         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      ((((sk_B) = (k1_xboole_0)))
% 0.21/0.54         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['19', '22'])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      ((((sk_B) != (sk_B)))
% 0.21/0.54         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.21/0.54             ((v3_relat_1 @ sk_A)) & 
% 0.21/0.54             ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (~ ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))) | 
% 0.21/0.54       ~ ((v3_relat_1 @ sk_A)) | (((sk_B) = (k1_xboole_0)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      ((![X32 : $i]:
% 0.21/0.54          (((X32) = (k1_xboole_0)) | ~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A)))) | 
% 0.21/0.54       ((v3_relat_1 @ sk_A))),
% 0.21/0.54      inference('split', [status(esa)], ['4'])).
% 0.21/0.54  thf(t69_enumset1, axiom,
% 0.21/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.54  thf('28', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.21/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.54  thf('30', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.21/0.54      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.54  thf(t38_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.21/0.54       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.54         ((r2_hidden @ X22 @ X23)
% 0.21/0.54          | ~ (r1_tarski @ (k2_tarski @ X22 @ X24) @ X23))),
% 0.21/0.54      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.54  thf('33', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['28', '32'])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X1 : $i, X3 : $i]:
% 0.21/0.54         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      ((![X32 : $i]:
% 0.21/0.54          (((X32) = (k1_xboole_0)) | ~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A))))
% 0.21/0.54         <= ((![X32 : $i]:
% 0.21/0.54                (((X32) = (k1_xboole_0))
% 0.21/0.54                 | ~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A)))))),
% 0.21/0.54      inference('split', [status(esa)], ['4'])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.21/0.54           | ((sk_C @ X0 @ (k2_relat_1 @ sk_A)) = (k1_xboole_0))))
% 0.21/0.54         <= ((![X32 : $i]:
% 0.21/0.54                (((X32) = (k1_xboole_0))
% 0.21/0.54                 | ~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (![X1 : $i, X3 : $i]:
% 0.21/0.54         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (~ (r2_hidden @ k1_xboole_0 @ X0)
% 0.21/0.54           | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.21/0.54           | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0)))
% 0.21/0.54         <= ((![X32 : $i]:
% 0.21/0.54                (((X32) = (k1_xboole_0))
% 0.21/0.54                 | ~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.21/0.54           | ~ (r2_hidden @ k1_xboole_0 @ X0)))
% 0.21/0.54         <= ((![X32 : $i]:
% 0.21/0.54                (((X32) = (k1_xboole_0))
% 0.21/0.54                 | ~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A)))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k1_tarski @ k1_xboole_0)))
% 0.21/0.54         <= ((![X32 : $i]:
% 0.21/0.54                (((X32) = (k1_xboole_0))
% 0.21/0.54                 | ~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['33', '39'])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X31 : $i]:
% 0.21/0.54         (~ (r1_tarski @ (k2_relat_1 @ X31) @ (k1_tarski @ k1_xboole_0))
% 0.21/0.54          | (v3_relat_1 @ X31)
% 0.21/0.54          | ~ (v1_relat_1 @ X31))),
% 0.21/0.54      inference('cnf', [status(esa)], [d15_relat_1])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (((~ (v1_relat_1 @ sk_A) | (v3_relat_1 @ sk_A)))
% 0.21/0.54         <= ((![X32 : $i]:
% 0.21/0.54                (((X32) = (k1_xboole_0))
% 0.21/0.54                 | ~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.54  thf('43', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (((v3_relat_1 @ sk_A))
% 0.21/0.54         <= ((![X32 : $i]:
% 0.21/0.54                (((X32) = (k1_xboole_0))
% 0.21/0.54                 | ~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A)))))),
% 0.21/0.54      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.54  thf('45', plain, ((~ (v3_relat_1 @ sk_A)) <= (~ ((v3_relat_1 @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (~
% 0.21/0.54       (![X32 : $i]:
% 0.21/0.54          (((X32) = (k1_xboole_0)) | ~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A)))) | 
% 0.21/0.54       ((v3_relat_1 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.54  thf('47', plain, ($false),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['1', '3', '26', '27', '46'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

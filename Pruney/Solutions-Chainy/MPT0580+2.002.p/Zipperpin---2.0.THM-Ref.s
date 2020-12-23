%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nlIVinFHYM

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:23 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 107 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  484 ( 763 expanded)
%              Number of equality atoms :   29 (  53 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_relat_1_type,type,(
    v3_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X38: $i] :
      ( ~ ( r2_hidden @ X38 @ ( k2_relat_1 @ sk_A ) )
      | ( X38 = k1_xboole_0 )
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
    ! [X37: $i] :
      ( ~ ( v3_relat_1 @ X37 )
      | ( r1_tarski @ ( k2_relat_1 @ X37 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ( m1_subset_1 @ X30 @ X31 )
      | ~ ( r2_hidden @ X30 @ X31 ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
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
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
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
    ( ! [X38: $i] :
        ( ( X38 = k1_xboole_0 )
        | ~ ( r2_hidden @ X38 @ ( k2_relat_1 @ sk_A ) ) )
    | ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('28',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('29',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) )
    | ( r2_hidden @ k1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('36',plain,(
    ! [X29: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r2_hidden @ k1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,
    ( ! [X38: $i] :
        ( ( X38 = k1_xboole_0 )
        | ~ ( r2_hidden @ X38 @ ( k2_relat_1 @ sk_A ) ) )
   <= ! [X38: $i] :
        ( ( X38 = k1_xboole_0 )
        | ~ ( r2_hidden @ X38 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) )
          = k1_xboole_0 ) )
   <= ! [X38: $i] :
        ( ( X38 = k1_xboole_0 )
        | ~ ( r2_hidden @ X38 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ k1_xboole_0 @ X0 )
        | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) )
   <= ! [X38: $i] :
        ( ( X38 = k1_xboole_0 )
        | ~ ( r2_hidden @ X38 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ k1_xboole_0 @ X0 ) )
   <= ! [X38: $i] :
        ( ( X38 = k1_xboole_0 )
        | ~ ( r2_hidden @ X38 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_tarski @ k1_xboole_0 ) )
   <= ! [X38: $i] :
        ( ( X38 = k1_xboole_0 )
        | ~ ( r2_hidden @ X38 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    ! [X37: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X37 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ( v3_relat_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d15_relat_1])).

thf('47',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( v3_relat_1 @ sk_A ) )
   <= ! [X38: $i] :
        ( ( X38 = k1_xboole_0 )
        | ~ ( r2_hidden @ X38 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v3_relat_1 @ sk_A )
   <= ! [X38: $i] :
        ( ( X38 = k1_xboole_0 )
        | ~ ( r2_hidden @ X38 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v3_relat_1 @ sk_A )
   <= ~ ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,
    ( ~ ! [X38: $i] :
          ( ( X38 = k1_xboole_0 )
          | ~ ( r2_hidden @ X38 @ ( k2_relat_1 @ sk_A ) ) )
    | ( v3_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','26','27','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nlIVinFHYM
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:30:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.53  % Solved by: fo/fo7.sh
% 0.37/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.53  % done 211 iterations in 0.070s
% 0.37/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.53  % SZS output start Refutation
% 0.37/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.53  thf(v3_relat_1_type, type, v3_relat_1: $i > $o).
% 0.37/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.53  thf(t184_relat_1, conjecture,
% 0.37/0.53    (![A:$i]:
% 0.37/0.53     ( ( v1_relat_1 @ A ) =>
% 0.37/0.53       ( ( v3_relat_1 @ A ) <=>
% 0.37/0.53         ( ![B:$i]:
% 0.37/0.53           ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) ) =>
% 0.37/0.53             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.37/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.53    (~( ![A:$i]:
% 0.37/0.53        ( ( v1_relat_1 @ A ) =>
% 0.37/0.53          ( ( v3_relat_1 @ A ) <=>
% 0.37/0.53            ( ![B:$i]:
% 0.37/0.53              ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) ) =>
% 0.37/0.53                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.37/0.53    inference('cnf.neg', [status(esa)], [t184_relat_1])).
% 0.37/0.53  thf('0', plain, ((((sk_B) != (k1_xboole_0)) | ~ (v3_relat_1 @ sk_A))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('1', plain, (~ (((sk_B) = (k1_xboole_0))) | ~ ((v3_relat_1 @ sk_A))),
% 0.37/0.53      inference('split', [status(esa)], ['0'])).
% 0.37/0.53  thf('2', plain,
% 0.37/0.53      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A)) | ~ (v3_relat_1 @ sk_A))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('3', plain,
% 0.37/0.53      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))) | ~ ((v3_relat_1 @ sk_A))),
% 0.37/0.53      inference('split', [status(esa)], ['2'])).
% 0.37/0.53  thf('4', plain,
% 0.37/0.53      (![X38 : $i]:
% 0.37/0.53         (~ (r2_hidden @ X38 @ (k2_relat_1 @ sk_A))
% 0.37/0.53          | ((X38) = (k1_xboole_0))
% 0.37/0.53          | (v3_relat_1 @ sk_A))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('5', plain, (((v3_relat_1 @ sk_A)) <= (((v3_relat_1 @ sk_A)))),
% 0.37/0.53      inference('split', [status(esa)], ['4'])).
% 0.37/0.53  thf('6', plain,
% 0.37/0.53      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.37/0.53         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.37/0.53      inference('split', [status(esa)], ['2'])).
% 0.37/0.53  thf(d15_relat_1, axiom,
% 0.37/0.53    (![A:$i]:
% 0.37/0.53     ( ( v1_relat_1 @ A ) =>
% 0.37/0.53       ( ( v3_relat_1 @ A ) <=>
% 0.37/0.53         ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_tarski @ k1_xboole_0 ) ) ) ))).
% 0.37/0.53  thf('7', plain,
% 0.37/0.53      (![X37 : $i]:
% 0.37/0.53         (~ (v3_relat_1 @ X37)
% 0.37/0.53          | (r1_tarski @ (k2_relat_1 @ X37) @ (k1_tarski @ k1_xboole_0))
% 0.37/0.53          | ~ (v1_relat_1 @ X37))),
% 0.37/0.53      inference('cnf', [status(esa)], [d15_relat_1])).
% 0.37/0.53  thf(d3_tarski, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.53  thf('8', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.53          | (r2_hidden @ X0 @ X2)
% 0.37/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.37/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.53  thf('9', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         (~ (v1_relat_1 @ X0)
% 0.37/0.53          | ~ (v3_relat_1 @ X0)
% 0.37/0.53          | (r2_hidden @ X1 @ (k1_tarski @ k1_xboole_0))
% 0.37/0.53          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.53  thf('10', plain,
% 0.37/0.53      ((((r2_hidden @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.37/0.53         | ~ (v3_relat_1 @ sk_A)
% 0.37/0.53         | ~ (v1_relat_1 @ sk_A)))
% 0.37/0.53         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['6', '9'])).
% 0.37/0.53  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('12', plain,
% 0.37/0.53      ((((r2_hidden @ sk_B @ (k1_tarski @ k1_xboole_0)) | ~ (v3_relat_1 @ sk_A)))
% 0.37/0.53         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.37/0.53      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.53  thf('13', plain,
% 0.37/0.53      (((r2_hidden @ sk_B @ (k1_tarski @ k1_xboole_0)))
% 0.37/0.53         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['5', '12'])).
% 0.37/0.53  thf(t1_subset, axiom,
% 0.37/0.53    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.37/0.53  thf('14', plain,
% 0.37/0.53      (![X30 : $i, X31 : $i]:
% 0.37/0.53         ((m1_subset_1 @ X30 @ X31) | ~ (r2_hidden @ X30 @ X31))),
% 0.37/0.53      inference('cnf', [status(esa)], [t1_subset])).
% 0.37/0.53  thf('15', plain,
% 0.37/0.53      (((m1_subset_1 @ sk_B @ (k1_tarski @ k1_xboole_0)))
% 0.37/0.53         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.53  thf(t1_zfmisc_1, axiom,
% 0.37/0.53    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.37/0.53  thf('16', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.37/0.53      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.37/0.53  thf(t3_subset, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.53  thf('17', plain,
% 0.37/0.53      (![X34 : $i, X35 : $i]:
% 0.37/0.53         ((r1_tarski @ X34 @ X35) | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 0.37/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.53  thf('18', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (~ (m1_subset_1 @ X0 @ (k1_tarski @ k1_xboole_0))
% 0.37/0.53          | (r1_tarski @ X0 @ k1_xboole_0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.53  thf('19', plain,
% 0.37/0.53      (((r1_tarski @ sk_B @ k1_xboole_0))
% 0.37/0.53         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['15', '18'])).
% 0.37/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.53  thf('20', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.37/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.53  thf(d10_xboole_0, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.53  thf('21', plain,
% 0.37/0.53      (![X4 : $i, X6 : $i]:
% 0.37/0.53         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.37/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.53  thf('22', plain,
% 0.37/0.53      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.53  thf('23', plain,
% 0.37/0.53      ((((sk_B) = (k1_xboole_0)))
% 0.37/0.53         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['19', '22'])).
% 0.37/0.53  thf('24', plain,
% 0.37/0.53      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.37/0.53      inference('split', [status(esa)], ['0'])).
% 0.37/0.53  thf('25', plain,
% 0.37/0.53      ((((sk_B) != (sk_B)))
% 0.37/0.53         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.37/0.53             ((v3_relat_1 @ sk_A)) & 
% 0.37/0.53             ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.53  thf('26', plain,
% 0.37/0.53      (~ ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))) | 
% 0.37/0.53       ~ ((v3_relat_1 @ sk_A)) | (((sk_B) = (k1_xboole_0)))),
% 0.37/0.53      inference('simplify', [status(thm)], ['25'])).
% 0.37/0.53  thf('27', plain,
% 0.37/0.53      ((![X38 : $i]:
% 0.37/0.53          (((X38) = (k1_xboole_0)) | ~ (r2_hidden @ X38 @ (k2_relat_1 @ sk_A)))) | 
% 0.37/0.53       ((v3_relat_1 @ sk_A))),
% 0.37/0.53      inference('split', [status(esa)], ['4'])).
% 0.37/0.53  thf('28', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.37/0.53      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.37/0.53  thf('29', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.37/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.53  thf('30', plain,
% 0.37/0.53      (![X34 : $i, X36 : $i]:
% 0.37/0.53         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 0.37/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.53  thf('31', plain,
% 0.37/0.53      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.53  thf('32', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_tarski @ k1_xboole_0))),
% 0.37/0.53      inference('sup+', [status(thm)], ['28', '31'])).
% 0.37/0.53  thf(t2_subset, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.37/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.37/0.53  thf('33', plain,
% 0.37/0.53      (![X32 : $i, X33 : $i]:
% 0.37/0.53         ((r2_hidden @ X32 @ X33)
% 0.37/0.53          | (v1_xboole_0 @ X33)
% 0.37/0.53          | ~ (m1_subset_1 @ X32 @ X33))),
% 0.37/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.37/0.53  thf('34', plain,
% 0.37/0.53      (((v1_xboole_0 @ (k1_tarski @ k1_xboole_0))
% 0.37/0.53        | (r2_hidden @ k1_xboole_0 @ (k1_tarski @ k1_xboole_0)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.53  thf('35', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.37/0.53      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.37/0.53  thf(fc1_subset_1, axiom,
% 0.37/0.53    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.53  thf('36', plain, (![X29 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 0.37/0.53      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.37/0.53  thf('37', plain, (~ (v1_xboole_0 @ (k1_tarski @ k1_xboole_0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.53  thf('38', plain, ((r2_hidden @ k1_xboole_0 @ (k1_tarski @ k1_xboole_0))),
% 0.37/0.53      inference('clc', [status(thm)], ['34', '37'])).
% 0.37/0.53  thf('39', plain,
% 0.37/0.53      (![X1 : $i, X3 : $i]:
% 0.37/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.53  thf('40', plain,
% 0.37/0.53      ((![X38 : $i]:
% 0.37/0.53          (((X38) = (k1_xboole_0)) | ~ (r2_hidden @ X38 @ (k2_relat_1 @ sk_A))))
% 0.37/0.53         <= ((![X38 : $i]:
% 0.37/0.53                (((X38) = (k1_xboole_0))
% 0.37/0.53                 | ~ (r2_hidden @ X38 @ (k2_relat_1 @ sk_A)))))),
% 0.37/0.53      inference('split', [status(esa)], ['4'])).
% 0.37/0.53  thf('41', plain,
% 0.37/0.53      ((![X0 : $i]:
% 0.37/0.53          ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.37/0.53           | ((sk_C @ X0 @ (k2_relat_1 @ sk_A)) = (k1_xboole_0))))
% 0.37/0.53         <= ((![X38 : $i]:
% 0.37/0.53                (((X38) = (k1_xboole_0))
% 0.37/0.53                 | ~ (r2_hidden @ X38 @ (k2_relat_1 @ sk_A)))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.53  thf('42', plain,
% 0.37/0.53      (![X1 : $i, X3 : $i]:
% 0.37/0.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.37/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.53  thf('43', plain,
% 0.37/0.53      ((![X0 : $i]:
% 0.37/0.53          (~ (r2_hidden @ k1_xboole_0 @ X0)
% 0.37/0.53           | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.37/0.53           | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0)))
% 0.37/0.53         <= ((![X38 : $i]:
% 0.37/0.53                (((X38) = (k1_xboole_0))
% 0.37/0.53                 | ~ (r2_hidden @ X38 @ (k2_relat_1 @ sk_A)))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['41', '42'])).
% 0.37/0.53  thf('44', plain,
% 0.37/0.53      ((![X0 : $i]:
% 0.37/0.53          ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.37/0.53           | ~ (r2_hidden @ k1_xboole_0 @ X0)))
% 0.37/0.53         <= ((![X38 : $i]:
% 0.37/0.53                (((X38) = (k1_xboole_0))
% 0.37/0.53                 | ~ (r2_hidden @ X38 @ (k2_relat_1 @ sk_A)))))),
% 0.37/0.53      inference('simplify', [status(thm)], ['43'])).
% 0.37/0.53  thf('45', plain,
% 0.37/0.53      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k1_tarski @ k1_xboole_0)))
% 0.37/0.53         <= ((![X38 : $i]:
% 0.37/0.53                (((X38) = (k1_xboole_0))
% 0.37/0.53                 | ~ (r2_hidden @ X38 @ (k2_relat_1 @ sk_A)))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['38', '44'])).
% 0.37/0.53  thf('46', plain,
% 0.37/0.53      (![X37 : $i]:
% 0.37/0.53         (~ (r1_tarski @ (k2_relat_1 @ X37) @ (k1_tarski @ k1_xboole_0))
% 0.37/0.53          | (v3_relat_1 @ X37)
% 0.37/0.53          | ~ (v1_relat_1 @ X37))),
% 0.37/0.53      inference('cnf', [status(esa)], [d15_relat_1])).
% 0.37/0.53  thf('47', plain,
% 0.37/0.53      (((~ (v1_relat_1 @ sk_A) | (v3_relat_1 @ sk_A)))
% 0.37/0.53         <= ((![X38 : $i]:
% 0.37/0.53                (((X38) = (k1_xboole_0))
% 0.37/0.53                 | ~ (r2_hidden @ X38 @ (k2_relat_1 @ sk_A)))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.53  thf('48', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('49', plain,
% 0.37/0.53      (((v3_relat_1 @ sk_A))
% 0.37/0.53         <= ((![X38 : $i]:
% 0.37/0.53                (((X38) = (k1_xboole_0))
% 0.37/0.53                 | ~ (r2_hidden @ X38 @ (k2_relat_1 @ sk_A)))))),
% 0.37/0.53      inference('demod', [status(thm)], ['47', '48'])).
% 0.37/0.53  thf('50', plain, ((~ (v3_relat_1 @ sk_A)) <= (~ ((v3_relat_1 @ sk_A)))),
% 0.37/0.53      inference('split', [status(esa)], ['0'])).
% 0.37/0.53  thf('51', plain,
% 0.37/0.53      (~
% 0.37/0.53       (![X38 : $i]:
% 0.37/0.53          (((X38) = (k1_xboole_0)) | ~ (r2_hidden @ X38 @ (k2_relat_1 @ sk_A)))) | 
% 0.37/0.53       ((v3_relat_1 @ sk_A))),
% 0.37/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.53  thf('52', plain, ($false),
% 0.37/0.53      inference('sat_resolution*', [status(thm)], ['1', '3', '26', '27', '51'])).
% 0.37/0.53  
% 0.37/0.53  % SZS output end Refutation
% 0.37/0.53  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

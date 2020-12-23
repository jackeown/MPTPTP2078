%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ecUJ4Uh7ev

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:23 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 106 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  481 ( 745 expanded)
%              Number of equality atoms :   33 (  56 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_relat_1_type,type,(
    v3_relat_1: $i > $o )).

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
    ! [X27: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k2_relat_1 @ sk_A ) )
      | ( X27 = k1_xboole_0 )
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
    ! [X26: $i] :
      ( ~ ( v3_relat_1 @ X26 )
      | ( r1_tarski @ ( k2_relat_1 @ X26 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
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

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ ( k3_tarski @ X19 ) )
      | ~ ( r2_hidden @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('15',plain,
    ( ( r1_tarski @ sk_B @ ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) )
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

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('17',plain,(
    ! [X20: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('18',plain,
    ( ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ sk_B @ k1_xboole_0 )
   <= ( ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','18'])).

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
    ( ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( r2_hidden @ X27 @ ( k2_relat_1 @ sk_A ) ) )
    | ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('28',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('29',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X22 ) @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('30',plain,(
    ! [X21: $i] :
      ( ( k2_subset_1 @ X21 )
      = X21 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('31',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r2_hidden @ X24 @ X25 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('34',plain,(
    ! [X23: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ k1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,
    ( ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( r2_hidden @ X27 @ ( k2_relat_1 @ sk_A ) ) )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( r2_hidden @ X27 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) )
          = k1_xboole_0 ) )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( r2_hidden @ X27 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ k1_xboole_0 @ X0 )
        | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( r2_hidden @ X27 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ k1_xboole_0 @ X0 ) )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( r2_hidden @ X27 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_tarski @ k1_xboole_0 ) )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( r2_hidden @ X27 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X26: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ( v3_relat_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d15_relat_1])).

thf('45',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( v3_relat_1 @ sk_A ) )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( r2_hidden @ X27 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v3_relat_1 @ sk_A )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( r2_hidden @ X27 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v3_relat_1 @ sk_A )
   <= ~ ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ~ ! [X27: $i] :
          ( ( X27 = k1_xboole_0 )
          | ~ ( r2_hidden @ X27 @ ( k2_relat_1 @ sk_A ) ) )
    | ( v3_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','26','27','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ecUJ4Uh7ev
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:50:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 121 iterations in 0.059s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.51  thf(v3_relat_1_type, type, v3_relat_1: $i > $o).
% 0.19/0.51  thf(t184_relat_1, conjecture,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ A ) =>
% 0.19/0.51       ( ( v3_relat_1 @ A ) <=>
% 0.19/0.51         ( ![B:$i]:
% 0.19/0.51           ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) ) =>
% 0.19/0.51             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i]:
% 0.19/0.51        ( ( v1_relat_1 @ A ) =>
% 0.19/0.51          ( ( v3_relat_1 @ A ) <=>
% 0.19/0.51            ( ![B:$i]:
% 0.19/0.51              ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) ) =>
% 0.19/0.51                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t184_relat_1])).
% 0.19/0.51  thf('0', plain, ((((sk_B) != (k1_xboole_0)) | ~ (v3_relat_1 @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('1', plain, (~ (((sk_B) = (k1_xboole_0))) | ~ ((v3_relat_1 @ sk_A))),
% 0.19/0.51      inference('split', [status(esa)], ['0'])).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A)) | ~ (v3_relat_1 @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('3', plain,
% 0.19/0.51      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))) | ~ ((v3_relat_1 @ sk_A))),
% 0.19/0.51      inference('split', [status(esa)], ['2'])).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      (![X27 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X27 @ (k2_relat_1 @ sk_A))
% 0.19/0.51          | ((X27) = (k1_xboole_0))
% 0.19/0.51          | (v3_relat_1 @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('5', plain, (((v3_relat_1 @ sk_A)) <= (((v3_relat_1 @ sk_A)))),
% 0.19/0.51      inference('split', [status(esa)], ['4'])).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.19/0.51         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.19/0.51      inference('split', [status(esa)], ['2'])).
% 0.19/0.51  thf(d15_relat_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ A ) =>
% 0.19/0.51       ( ( v3_relat_1 @ A ) <=>
% 0.19/0.51         ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_tarski @ k1_xboole_0 ) ) ) ))).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      (![X26 : $i]:
% 0.19/0.51         (~ (v3_relat_1 @ X26)
% 0.19/0.51          | (r1_tarski @ (k2_relat_1 @ X26) @ (k1_tarski @ k1_xboole_0))
% 0.19/0.51          | ~ (v1_relat_1 @ X26))),
% 0.19/0.51      inference('cnf', [status(esa)], [d15_relat_1])).
% 0.19/0.51  thf(d3_tarski, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.51  thf('8', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.51          | (r2_hidden @ X0 @ X2)
% 0.19/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.51  thf('9', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X0)
% 0.19/0.51          | ~ (v3_relat_1 @ X0)
% 0.19/0.51          | (r2_hidden @ X1 @ (k1_tarski @ k1_xboole_0))
% 0.19/0.51          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.51  thf('10', plain,
% 0.19/0.51      ((((r2_hidden @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.19/0.51         | ~ (v3_relat_1 @ sk_A)
% 0.19/0.51         | ~ (v1_relat_1 @ sk_A)))
% 0.19/0.51         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['6', '9'])).
% 0.19/0.51  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('12', plain,
% 0.19/0.51      ((((r2_hidden @ sk_B @ (k1_tarski @ k1_xboole_0)) | ~ (v3_relat_1 @ sk_A)))
% 0.19/0.51         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.19/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.51  thf('13', plain,
% 0.19/0.51      (((r2_hidden @ sk_B @ (k1_tarski @ k1_xboole_0)))
% 0.19/0.51         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['5', '12'])).
% 0.19/0.51  thf(l49_zfmisc_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.19/0.51  thf('14', plain,
% 0.19/0.51      (![X18 : $i, X19 : $i]:
% 0.19/0.51         ((r1_tarski @ X18 @ (k3_tarski @ X19)) | ~ (r2_hidden @ X18 @ X19))),
% 0.19/0.51      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.19/0.51  thf('15', plain,
% 0.19/0.51      (((r1_tarski @ sk_B @ (k3_tarski @ (k1_tarski @ k1_xboole_0))))
% 0.19/0.51         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.51  thf(t1_zfmisc_1, axiom,
% 0.19/0.51    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.19/0.51  thf('16', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.19/0.51      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.19/0.51  thf(t99_zfmisc_1, axiom,
% 0.19/0.51    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.19/0.51  thf('17', plain, (![X20 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X20)) = (X20))),
% 0.19/0.51      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.19/0.51  thf('18', plain, (((k3_tarski @ (k1_tarski @ k1_xboole_0)) = (k1_xboole_0))),
% 0.19/0.51      inference('sup+', [status(thm)], ['16', '17'])).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      (((r1_tarski @ sk_B @ k1_xboole_0))
% 0.19/0.51         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.19/0.51      inference('demod', [status(thm)], ['15', '18'])).
% 0.19/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.51  thf('20', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.19/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.51  thf(d10_xboole_0, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.51  thf('21', plain,
% 0.19/0.51      (![X4 : $i, X6 : $i]:
% 0.19/0.51         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.19/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.51  thf('22', plain,
% 0.19/0.51      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.51  thf('23', plain,
% 0.19/0.51      ((((sk_B) = (k1_xboole_0)))
% 0.19/0.51         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['19', '22'])).
% 0.19/0.51  thf('24', plain,
% 0.19/0.51      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.19/0.51      inference('split', [status(esa)], ['0'])).
% 0.19/0.51  thf('25', plain,
% 0.19/0.51      ((((sk_B) != (sk_B)))
% 0.19/0.51         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.19/0.51             ((v3_relat_1 @ sk_A)) & 
% 0.19/0.51             ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.51  thf('26', plain,
% 0.19/0.51      (~ ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))) | 
% 0.19/0.51       ~ ((v3_relat_1 @ sk_A)) | (((sk_B) = (k1_xboole_0)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['25'])).
% 0.19/0.51  thf('27', plain,
% 0.19/0.51      ((![X27 : $i]:
% 0.19/0.51          (((X27) = (k1_xboole_0)) | ~ (r2_hidden @ X27 @ (k2_relat_1 @ sk_A)))) | 
% 0.19/0.51       ((v3_relat_1 @ sk_A))),
% 0.19/0.51      inference('split', [status(esa)], ['4'])).
% 0.19/0.51  thf('28', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.19/0.51      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.19/0.51  thf(dt_k2_subset_1, axiom,
% 0.19/0.51    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.51  thf('29', plain,
% 0.19/0.51      (![X22 : $i]: (m1_subset_1 @ (k2_subset_1 @ X22) @ (k1_zfmisc_1 @ X22))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.19/0.51  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.51  thf('30', plain, (![X21 : $i]: ((k2_subset_1 @ X21) = (X21))),
% 0.19/0.51      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.51  thf('31', plain, (![X22 : $i]: (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X22))),
% 0.19/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.19/0.51  thf(t2_subset, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.19/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.51  thf('32', plain,
% 0.19/0.51      (![X24 : $i, X25 : $i]:
% 0.19/0.51         ((r2_hidden @ X24 @ X25)
% 0.19/0.51          | (v1_xboole_0 @ X25)
% 0.19/0.51          | ~ (m1_subset_1 @ X24 @ X25))),
% 0.19/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.19/0.51  thf('33', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.19/0.51          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.51  thf(fc1_subset_1, axiom,
% 0.19/0.51    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.51  thf('34', plain, (![X23 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X23))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.19/0.51  thf('35', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.51      inference('clc', [status(thm)], ['33', '34'])).
% 0.19/0.51  thf('36', plain, ((r2_hidden @ k1_xboole_0 @ (k1_tarski @ k1_xboole_0))),
% 0.19/0.51      inference('sup+', [status(thm)], ['28', '35'])).
% 0.19/0.51  thf('37', plain,
% 0.19/0.51      (![X1 : $i, X3 : $i]:
% 0.19/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.51  thf('38', plain,
% 0.19/0.51      ((![X27 : $i]:
% 0.19/0.51          (((X27) = (k1_xboole_0)) | ~ (r2_hidden @ X27 @ (k2_relat_1 @ sk_A))))
% 0.19/0.51         <= ((![X27 : $i]:
% 0.19/0.51                (((X27) = (k1_xboole_0))
% 0.19/0.51                 | ~ (r2_hidden @ X27 @ (k2_relat_1 @ sk_A)))))),
% 0.19/0.51      inference('split', [status(esa)], ['4'])).
% 0.19/0.51  thf('39', plain,
% 0.19/0.51      ((![X0 : $i]:
% 0.19/0.51          ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.19/0.51           | ((sk_C @ X0 @ (k2_relat_1 @ sk_A)) = (k1_xboole_0))))
% 0.19/0.51         <= ((![X27 : $i]:
% 0.19/0.51                (((X27) = (k1_xboole_0))
% 0.19/0.51                 | ~ (r2_hidden @ X27 @ (k2_relat_1 @ sk_A)))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.19/0.51  thf('40', plain,
% 0.19/0.51      (![X1 : $i, X3 : $i]:
% 0.19/0.51         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.19/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.51  thf('41', plain,
% 0.19/0.51      ((![X0 : $i]:
% 0.19/0.51          (~ (r2_hidden @ k1_xboole_0 @ X0)
% 0.19/0.51           | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.19/0.51           | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0)))
% 0.19/0.51         <= ((![X27 : $i]:
% 0.19/0.51                (((X27) = (k1_xboole_0))
% 0.19/0.51                 | ~ (r2_hidden @ X27 @ (k2_relat_1 @ sk_A)))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.51  thf('42', plain,
% 0.19/0.51      ((![X0 : $i]:
% 0.19/0.51          ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.19/0.51           | ~ (r2_hidden @ k1_xboole_0 @ X0)))
% 0.19/0.51         <= ((![X27 : $i]:
% 0.19/0.51                (((X27) = (k1_xboole_0))
% 0.19/0.51                 | ~ (r2_hidden @ X27 @ (k2_relat_1 @ sk_A)))))),
% 0.19/0.51      inference('simplify', [status(thm)], ['41'])).
% 0.19/0.51  thf('43', plain,
% 0.19/0.51      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k1_tarski @ k1_xboole_0)))
% 0.19/0.51         <= ((![X27 : $i]:
% 0.19/0.51                (((X27) = (k1_xboole_0))
% 0.19/0.51                 | ~ (r2_hidden @ X27 @ (k2_relat_1 @ sk_A)))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['36', '42'])).
% 0.19/0.51  thf('44', plain,
% 0.19/0.51      (![X26 : $i]:
% 0.19/0.51         (~ (r1_tarski @ (k2_relat_1 @ X26) @ (k1_tarski @ k1_xboole_0))
% 0.19/0.51          | (v3_relat_1 @ X26)
% 0.19/0.51          | ~ (v1_relat_1 @ X26))),
% 0.19/0.51      inference('cnf', [status(esa)], [d15_relat_1])).
% 0.19/0.51  thf('45', plain,
% 0.19/0.51      (((~ (v1_relat_1 @ sk_A) | (v3_relat_1 @ sk_A)))
% 0.19/0.51         <= ((![X27 : $i]:
% 0.19/0.51                (((X27) = (k1_xboole_0))
% 0.19/0.51                 | ~ (r2_hidden @ X27 @ (k2_relat_1 @ sk_A)))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.19/0.51  thf('46', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('47', plain,
% 0.19/0.51      (((v3_relat_1 @ sk_A))
% 0.19/0.51         <= ((![X27 : $i]:
% 0.19/0.51                (((X27) = (k1_xboole_0))
% 0.19/0.51                 | ~ (r2_hidden @ X27 @ (k2_relat_1 @ sk_A)))))),
% 0.19/0.51      inference('demod', [status(thm)], ['45', '46'])).
% 0.19/0.51  thf('48', plain, ((~ (v3_relat_1 @ sk_A)) <= (~ ((v3_relat_1 @ sk_A)))),
% 0.19/0.51      inference('split', [status(esa)], ['0'])).
% 0.19/0.51  thf('49', plain,
% 0.19/0.51      (~
% 0.19/0.51       (![X27 : $i]:
% 0.19/0.51          (((X27) = (k1_xboole_0)) | ~ (r2_hidden @ X27 @ (k2_relat_1 @ sk_A)))) | 
% 0.19/0.51       ((v3_relat_1 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.51  thf('50', plain, ($false),
% 0.19/0.51      inference('sat_resolution*', [status(thm)], ['1', '3', '26', '27', '49'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

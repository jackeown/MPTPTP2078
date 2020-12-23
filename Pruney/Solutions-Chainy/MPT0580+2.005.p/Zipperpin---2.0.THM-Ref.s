%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q8N5XxZbH2

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:23 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 107 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  507 ( 781 expanded)
%              Number of equality atoms :   36 (  61 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_relat_1_type,type,(
    v3_relat_1: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('8',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('9',plain,(
    ! [X31: $i] :
      ( ~ ( v3_relat_1 @ X31 )
      | ( r1_tarski @ ( k2_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v3_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v3_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v3_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('16',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ ( k3_tarski @ X24 ) )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('17',plain,
    ( ( r1_tarski @ sk_B @ ( k3_tarski @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) )
   <= ( ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('19',plain,(
    ! [X26: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('20',plain,
    ( ( k3_tarski @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_tarski @ sk_B @ k1_xboole_0 )
   <= ( ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v3_relat_1 @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ sk_A ) ) )
    | ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('30',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    ! [X26: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('33',plain,(
    ! [X25: $i] :
      ( r1_tarski @ X25 @ ( k1_zfmisc_1 @ ( k3_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ ( k2_tarski @ X27 @ X29 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,
    ( ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) )
          = k1_xboole_0 ) )
   <= ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ sk_A ) ) ) ),
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
   <= ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ k1_xboole_0 @ X0 ) )
   <= ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X31: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ( v3_relat_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d15_relat_1])).

thf('45',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('46',plain,(
    ! [X31: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v3_relat_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( v3_relat_1 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v3_relat_1 @ sk_A )
   <= ! [X32: $i] :
        ( ( X32 = k1_xboole_0 )
        | ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v3_relat_1 @ sk_A )
   <= ~ ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,
    ( ~ ! [X32: $i] :
          ( ( X32 = k1_xboole_0 )
          | ~ ( r2_hidden @ X32 @ ( k2_relat_1 @ sk_A ) ) )
    | ( v3_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','28','29','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q8N5XxZbH2
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:02:22 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 158 iterations in 0.077s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.57  thf(v3_relat_1_type, type, v3_relat_1: $i > $o).
% 0.39/0.57  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.39/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.57  thf(t184_relat_1, conjecture,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ A ) =>
% 0.39/0.57       ( ( v3_relat_1 @ A ) <=>
% 0.39/0.57         ( ![B:$i]:
% 0.39/0.57           ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) ) =>
% 0.39/0.57             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i]:
% 0.39/0.57        ( ( v1_relat_1 @ A ) =>
% 0.39/0.57          ( ( v3_relat_1 @ A ) <=>
% 0.39/0.57            ( ![B:$i]:
% 0.39/0.57              ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) ) =>
% 0.39/0.57                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t184_relat_1])).
% 0.39/0.57  thf('0', plain, ((((sk_B) != (k1_xboole_0)) | ~ (v3_relat_1 @ sk_A))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('1', plain, (~ (((sk_B) = (k1_xboole_0))) | ~ ((v3_relat_1 @ sk_A))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A)) | ~ (v3_relat_1 @ sk_A))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))) | ~ ((v3_relat_1 @ sk_A))),
% 0.39/0.57      inference('split', [status(esa)], ['2'])).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (![X32 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A))
% 0.39/0.57          | ((X32) = (k1_xboole_0))
% 0.39/0.57          | (v3_relat_1 @ sk_A))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('5', plain, (((v3_relat_1 @ sk_A)) <= (((v3_relat_1 @ sk_A)))),
% 0.39/0.57      inference('split', [status(esa)], ['4'])).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.39/0.57         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.39/0.57      inference('split', [status(esa)], ['2'])).
% 0.39/0.57  thf(d15_relat_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ A ) =>
% 0.39/0.57       ( ( v3_relat_1 @ A ) <=>
% 0.39/0.57         ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_tarski @ k1_xboole_0 ) ) ) ))).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      (![X31 : $i]:
% 0.39/0.57         (~ (v3_relat_1 @ X31)
% 0.39/0.57          | (r1_tarski @ (k2_relat_1 @ X31) @ (k1_tarski @ k1_xboole_0))
% 0.39/0.57          | ~ (v1_relat_1 @ X31))),
% 0.39/0.57      inference('cnf', [status(esa)], [d15_relat_1])).
% 0.39/0.57  thf(t1_zfmisc_1, axiom,
% 0.39/0.57    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.39/0.57  thf('8', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X31 : $i]:
% 0.39/0.57         (~ (v3_relat_1 @ X31)
% 0.39/0.57          | (r1_tarski @ (k2_relat_1 @ X31) @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.39/0.57          | ~ (v1_relat_1 @ X31))),
% 0.39/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.39/0.57  thf(d3_tarski, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.39/0.57          | (r2_hidden @ X0 @ X2)
% 0.39/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X0)
% 0.39/0.57          | ~ (v3_relat_1 @ X0)
% 0.39/0.57          | (r2_hidden @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.39/0.57          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      ((((r2_hidden @ sk_B @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.39/0.57         | ~ (v3_relat_1 @ sk_A)
% 0.39/0.57         | ~ (v1_relat_1 @ sk_A)))
% 0.39/0.57         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['6', '11'])).
% 0.39/0.57  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      ((((r2_hidden @ sk_B @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.39/0.57         | ~ (v3_relat_1 @ sk_A)))
% 0.39/0.57         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.39/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      (((r2_hidden @ sk_B @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.39/0.57         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['5', '14'])).
% 0.39/0.57  thf(l49_zfmisc_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (![X23 : $i, X24 : $i]:
% 0.39/0.57         ((r1_tarski @ X23 @ (k3_tarski @ X24)) | ~ (r2_hidden @ X23 @ X24))),
% 0.39/0.57      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (((r1_tarski @ sk_B @ (k3_tarski @ (k1_zfmisc_1 @ k1_xboole_0))))
% 0.39/0.57         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.57  thf('18', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.39/0.57  thf(t31_zfmisc_1, axiom,
% 0.39/0.57    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.39/0.57  thf('19', plain, (![X26 : $i]: ((k3_tarski @ (k1_tarski @ X26)) = (X26))),
% 0.39/0.57      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (((k3_tarski @ (k1_zfmisc_1 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['18', '19'])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      (((r1_tarski @ sk_B @ k1_xboole_0))
% 0.39/0.57         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.39/0.57      inference('demod', [status(thm)], ['17', '20'])).
% 0.39/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.39/0.57  thf('22', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.39/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.57  thf(d10_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      (![X4 : $i, X6 : $i]:
% 0.39/0.57         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.39/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      ((((sk_B) = (k1_xboole_0)))
% 0.39/0.57         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['21', '24'])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      ((((sk_B) != (sk_B)))
% 0.39/0.57         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.39/0.57             ((v3_relat_1 @ sk_A)) & 
% 0.39/0.57             ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (~ ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))) | 
% 0.39/0.57       ~ ((v3_relat_1 @ sk_A)) | (((sk_B) = (k1_xboole_0)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['27'])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      ((![X32 : $i]:
% 0.39/0.57          (((X32) = (k1_xboole_0)) | ~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A)))) | 
% 0.39/0.57       ((v3_relat_1 @ sk_A))),
% 0.39/0.57      inference('split', [status(esa)], ['4'])).
% 0.39/0.57  thf(t69_enumset1, axiom,
% 0.39/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.57  thf('30', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.39/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.57  thf('31', plain, (![X26 : $i]: ((k3_tarski @ (k1_tarski @ X26)) = (X26))),
% 0.39/0.57      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.39/0.57  thf('32', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['30', '31'])).
% 0.39/0.57  thf(t100_zfmisc_1, axiom,
% 0.39/0.57    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.39/0.57  thf('33', plain,
% 0.39/0.57      (![X25 : $i]: (r1_tarski @ X25 @ (k1_zfmisc_1 @ (k3_tarski @ X25)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.39/0.57  thf('34', plain,
% 0.39/0.57      (![X0 : $i]: (r1_tarski @ (k2_tarski @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['32', '33'])).
% 0.39/0.57  thf(t38_zfmisc_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.39/0.57       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.39/0.57         ((r2_hidden @ X27 @ X28)
% 0.39/0.57          | ~ (r1_tarski @ (k2_tarski @ X27 @ X29) @ X28))),
% 0.39/0.57      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.39/0.57  thf('36', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      (![X1 : $i, X3 : $i]:
% 0.39/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.57  thf('38', plain,
% 0.39/0.57      ((![X32 : $i]:
% 0.39/0.57          (((X32) = (k1_xboole_0)) | ~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A))))
% 0.39/0.57         <= ((![X32 : $i]:
% 0.39/0.57                (((X32) = (k1_xboole_0))
% 0.39/0.57                 | ~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A)))))),
% 0.39/0.57      inference('split', [status(esa)], ['4'])).
% 0.39/0.57  thf('39', plain,
% 0.39/0.57      ((![X0 : $i]:
% 0.39/0.57          ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.39/0.57           | ((sk_C @ X0 @ (k2_relat_1 @ sk_A)) = (k1_xboole_0))))
% 0.39/0.57         <= ((![X32 : $i]:
% 0.39/0.57                (((X32) = (k1_xboole_0))
% 0.39/0.57                 | ~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A)))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      (![X1 : $i, X3 : $i]:
% 0.39/0.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.57  thf('41', plain,
% 0.39/0.57      ((![X0 : $i]:
% 0.39/0.57          (~ (r2_hidden @ k1_xboole_0 @ X0)
% 0.39/0.57           | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.39/0.57           | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0)))
% 0.39/0.57         <= ((![X32 : $i]:
% 0.39/0.57                (((X32) = (k1_xboole_0))
% 0.39/0.57                 | ~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A)))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.39/0.57  thf('42', plain,
% 0.39/0.57      ((![X0 : $i]:
% 0.39/0.57          ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.39/0.57           | ~ (r2_hidden @ k1_xboole_0 @ X0)))
% 0.39/0.57         <= ((![X32 : $i]:
% 0.39/0.57                (((X32) = (k1_xboole_0))
% 0.39/0.57                 | ~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A)))))),
% 0.39/0.57      inference('simplify', [status(thm)], ['41'])).
% 0.39/0.57  thf('43', plain,
% 0.39/0.57      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.39/0.57         <= ((![X32 : $i]:
% 0.39/0.57                (((X32) = (k1_xboole_0))
% 0.39/0.57                 | ~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A)))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['36', '42'])).
% 0.39/0.57  thf('44', plain,
% 0.39/0.57      (![X31 : $i]:
% 0.39/0.57         (~ (r1_tarski @ (k2_relat_1 @ X31) @ (k1_tarski @ k1_xboole_0))
% 0.39/0.57          | (v3_relat_1 @ X31)
% 0.39/0.57          | ~ (v1_relat_1 @ X31))),
% 0.39/0.57      inference('cnf', [status(esa)], [d15_relat_1])).
% 0.39/0.57  thf('45', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.39/0.57  thf('46', plain,
% 0.39/0.57      (![X31 : $i]:
% 0.39/0.57         (~ (r1_tarski @ (k2_relat_1 @ X31) @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.39/0.57          | (v3_relat_1 @ X31)
% 0.39/0.57          | ~ (v1_relat_1 @ X31))),
% 0.39/0.57      inference('demod', [status(thm)], ['44', '45'])).
% 0.39/0.57  thf('47', plain,
% 0.39/0.57      (((~ (v1_relat_1 @ sk_A) | (v3_relat_1 @ sk_A)))
% 0.39/0.57         <= ((![X32 : $i]:
% 0.39/0.57                (((X32) = (k1_xboole_0))
% 0.39/0.57                 | ~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A)))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['43', '46'])).
% 0.39/0.57  thf('48', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('49', plain,
% 0.39/0.57      (((v3_relat_1 @ sk_A))
% 0.39/0.57         <= ((![X32 : $i]:
% 0.39/0.57                (((X32) = (k1_xboole_0))
% 0.39/0.57                 | ~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A)))))),
% 0.39/0.57      inference('demod', [status(thm)], ['47', '48'])).
% 0.39/0.57  thf('50', plain, ((~ (v3_relat_1 @ sk_A)) <= (~ ((v3_relat_1 @ sk_A)))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf('51', plain,
% 0.39/0.57      (~
% 0.39/0.57       (![X32 : $i]:
% 0.39/0.57          (((X32) = (k1_xboole_0)) | ~ (r2_hidden @ X32 @ (k2_relat_1 @ sk_A)))) | 
% 0.39/0.57       ((v3_relat_1 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.39/0.57  thf('52', plain, ($false),
% 0.39/0.57      inference('sat_resolution*', [status(thm)], ['1', '3', '28', '29', '51'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.42/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

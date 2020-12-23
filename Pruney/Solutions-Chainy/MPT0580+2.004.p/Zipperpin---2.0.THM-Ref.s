%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gbEJdQSGvi

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 105 expanded)
%              Number of leaves         :   26 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  508 ( 772 expanded)
%              Number of equality atoms :   34 (  57 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_relat_1_type,type,(
    v3_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X35: $i] :
      ( ~ ( r2_hidden @ X35 @ ( k2_relat_1 @ sk_A ) )
      | ( X35 = k1_xboole_0 )
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
    ! [X34: $i] :
      ( ~ ( v3_relat_1 @ X34 )
      | ( r1_tarski @ ( k2_relat_1 @ X34 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d15_relat_1])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('8',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('9',plain,(
    ! [X34: $i] :
      ( ~ ( v3_relat_1 @ X34 )
      | ( r1_tarski @ ( k2_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ X24 @ ( k3_tarski @ X25 ) )
      | ~ ( r2_hidden @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('17',plain,
    ( ( r1_tarski @ sk_B @ ( k3_tarski @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) )
   <= ( ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('18',plain,(
    ! [X33: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('19',plain,
    ( ( r1_tarski @ sk_B @ k1_xboole_0 )
   <= ( ( v3_relat_1 @ sk_A )
      & ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

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
    ( ! [X35: $i] :
        ( ( X35 = k1_xboole_0 )
        | ~ ( r2_hidden @ X35 @ ( k2_relat_1 @ sk_A ) ) )
    | ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('28',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('30',plain,(
    ! [X28: $i] :
      ( r1_tarski @ X28 @ ( k1_zfmisc_1 @ ( k3_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X29 @ X30 )
      | ~ ( r1_tarski @ ( k2_tarski @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,
    ( ! [X35: $i] :
        ( ( X35 = k1_xboole_0 )
        | ~ ( r2_hidden @ X35 @ ( k2_relat_1 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ( X35 = k1_xboole_0 )
        | ~ ( r2_hidden @ X35 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) )
          = k1_xboole_0 ) )
   <= ! [X35: $i] :
        ( ( X35 = k1_xboole_0 )
        | ~ ( r2_hidden @ X35 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ k1_xboole_0 @ X0 )
        | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) )
   <= ! [X35: $i] :
        ( ( X35 = k1_xboole_0 )
        | ~ ( r2_hidden @ X35 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ k1_xboole_0 @ X0 ) )
   <= ! [X35: $i] :
        ( ( X35 = k1_xboole_0 )
        | ~ ( r2_hidden @ X35 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ! [X35: $i] :
        ( ( X35 = k1_xboole_0 )
        | ~ ( r2_hidden @ X35 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    ! [X34: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X34 ) @ ( k1_tarski @ k1_xboole_0 ) )
      | ( v3_relat_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d15_relat_1])).

thf('43',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('44',plain,(
    ! [X34: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v3_relat_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( v3_relat_1 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( X35 = k1_xboole_0 )
        | ~ ( r2_hidden @ X35 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v3_relat_1 @ sk_A )
   <= ! [X35: $i] :
        ( ( X35 = k1_xboole_0 )
        | ~ ( r2_hidden @ X35 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v3_relat_1 @ sk_A )
   <= ~ ( v3_relat_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ~ ! [X35: $i] :
          ( ( X35 = k1_xboole_0 )
          | ~ ( r2_hidden @ X35 @ ( k2_relat_1 @ sk_A ) ) )
    | ( v3_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','26','27','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gbEJdQSGvi
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:48:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 120 iterations in 0.039s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(v3_relat_1_type, type, v3_relat_1: $i > $o).
% 0.20/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(t184_relat_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( v3_relat_1 @ A ) <=>
% 0.20/0.48         ( ![B:$i]:
% 0.20/0.48           ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) ) =>
% 0.20/0.48             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( v1_relat_1 @ A ) =>
% 0.20/0.48          ( ( v3_relat_1 @ A ) <=>
% 0.20/0.48            ( ![B:$i]:
% 0.20/0.48              ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) ) =>
% 0.20/0.48                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t184_relat_1])).
% 0.20/0.48  thf('0', plain, ((((sk_B) != (k1_xboole_0)) | ~ (v3_relat_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain, (~ (((sk_B) = (k1_xboole_0))) | ~ ((v3_relat_1 @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A)) | ~ (v3_relat_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))) | ~ ((v3_relat_1 @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X35 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X35 @ (k2_relat_1 @ sk_A))
% 0.20/0.48          | ((X35) = (k1_xboole_0))
% 0.20/0.48          | (v3_relat_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('5', plain, (((v3_relat_1 @ sk_A)) <= (((v3_relat_1 @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['4'])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.20/0.48         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf(d15_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( v3_relat_1 @ A ) <=>
% 0.20/0.48         ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_tarski @ k1_xboole_0 ) ) ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X34 : $i]:
% 0.20/0.48         (~ (v3_relat_1 @ X34)
% 0.20/0.48          | (r1_tarski @ (k2_relat_1 @ X34) @ (k1_tarski @ k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X34))),
% 0.20/0.48      inference('cnf', [status(esa)], [d15_relat_1])).
% 0.20/0.48  thf(t1_zfmisc_1, axiom,
% 0.20/0.48    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.20/0.48  thf('8', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X34 : $i]:
% 0.20/0.48         (~ (v3_relat_1 @ X34)
% 0.20/0.48          | (r1_tarski @ (k2_relat_1 @ X34) @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X34))),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf(d3_tarski, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.48          | (r2_hidden @ X0 @ X2)
% 0.20/0.48          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v3_relat_1 @ X0)
% 0.20/0.48          | (r2_hidden @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.20/0.48          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      ((((r2_hidden @ sk_B @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.20/0.48         | ~ (v3_relat_1 @ sk_A)
% 0.20/0.48         | ~ (v1_relat_1 @ sk_A)))
% 0.20/0.48         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '11'])).
% 0.20/0.48  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      ((((r2_hidden @ sk_B @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.20/0.48         | ~ (v3_relat_1 @ sk_A)))
% 0.20/0.48         <= (((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (((r2_hidden @ sk_B @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.20/0.48         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '14'])).
% 0.20/0.48  thf(l49_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X24 : $i, X25 : $i]:
% 0.20/0.48         ((r1_tarski @ X24 @ (k3_tarski @ X25)) | ~ (r2_hidden @ X24 @ X25))),
% 0.20/0.48      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (((r1_tarski @ sk_B @ (k3_tarski @ (k1_zfmisc_1 @ k1_xboole_0))))
% 0.20/0.48         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf(t99_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.20/0.48  thf('18', plain, (![X33 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X33)) = (X33))),
% 0.20/0.48      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (((r1_tarski @ sk_B @ k1_xboole_0))
% 0.20/0.48         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.48  thf('20', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.48  thf(d10_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X4 : $i, X6 : $i]:
% 0.20/0.48         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      ((((sk_B) = (k1_xboole_0)))
% 0.20/0.48         <= (((v3_relat_1 @ sk_A)) & ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      ((((sk_B) != (sk_B)))
% 0.20/0.48         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.20/0.48             ((v3_relat_1 @ sk_A)) & 
% 0.20/0.48             ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (~ ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_A))) | 
% 0.20/0.48       ~ ((v3_relat_1 @ sk_A)) | (((sk_B) = (k1_xboole_0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      ((![X35 : $i]:
% 0.20/0.48          (((X35) = (k1_xboole_0)) | ~ (r2_hidden @ X35 @ (k2_relat_1 @ sk_A)))) | 
% 0.20/0.48       ((v3_relat_1 @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['4'])).
% 0.20/0.48  thf(t1_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.48  thf('28', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.48  thf(l51_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X26 : $i, X27 : $i]:
% 0.20/0.48         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 0.20/0.48      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.48  thf(t100_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (![X28 : $i]: (r1_tarski @ X28 @ (k1_zfmisc_1 @ (k3_tarski @ X28)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (r1_tarski @ (k2_tarski @ X1 @ X0) @ 
% 0.20/0.48          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['29', '30'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (r1_tarski @ (k2_tarski @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['28', '31'])).
% 0.20/0.48  thf(t38_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.20/0.48       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.48         ((r2_hidden @ X29 @ X30)
% 0.20/0.48          | ~ (r1_tarski @ (k2_tarski @ X29 @ X31) @ X30))),
% 0.20/0.48      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.48  thf('34', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X1 : $i, X3 : $i]:
% 0.20/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      ((![X35 : $i]:
% 0.20/0.48          (((X35) = (k1_xboole_0)) | ~ (r2_hidden @ X35 @ (k2_relat_1 @ sk_A))))
% 0.20/0.48         <= ((![X35 : $i]:
% 0.20/0.48                (((X35) = (k1_xboole_0))
% 0.20/0.48                 | ~ (r2_hidden @ X35 @ (k2_relat_1 @ sk_A)))))),
% 0.20/0.48      inference('split', [status(esa)], ['4'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      ((![X0 : $i]:
% 0.20/0.48          ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.20/0.48           | ((sk_C @ X0 @ (k2_relat_1 @ sk_A)) = (k1_xboole_0))))
% 0.20/0.48         <= ((![X35 : $i]:
% 0.20/0.48                (((X35) = (k1_xboole_0))
% 0.20/0.48                 | ~ (r2_hidden @ X35 @ (k2_relat_1 @ sk_A)))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (![X1 : $i, X3 : $i]:
% 0.20/0.48         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      ((![X0 : $i]:
% 0.20/0.48          (~ (r2_hidden @ k1_xboole_0 @ X0)
% 0.20/0.48           | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.20/0.48           | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0)))
% 0.20/0.48         <= ((![X35 : $i]:
% 0.20/0.48                (((X35) = (k1_xboole_0))
% 0.20/0.48                 | ~ (r2_hidden @ X35 @ (k2_relat_1 @ sk_A)))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      ((![X0 : $i]:
% 0.20/0.48          ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 0.20/0.48           | ~ (r2_hidden @ k1_xboole_0 @ X0)))
% 0.20/0.48         <= ((![X35 : $i]:
% 0.20/0.48                (((X35) = (k1_xboole_0))
% 0.20/0.48                 | ~ (r2_hidden @ X35 @ (k2_relat_1 @ sk_A)))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.20/0.48         <= ((![X35 : $i]:
% 0.20/0.48                (((X35) = (k1_xboole_0))
% 0.20/0.48                 | ~ (r2_hidden @ X35 @ (k2_relat_1 @ sk_A)))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['34', '40'])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (![X34 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k2_relat_1 @ X34) @ (k1_tarski @ k1_xboole_0))
% 0.20/0.48          | (v3_relat_1 @ X34)
% 0.20/0.48          | ~ (v1_relat_1 @ X34))),
% 0.20/0.48      inference('cnf', [status(esa)], [d15_relat_1])).
% 0.20/0.48  thf('43', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (![X34 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k2_relat_1 @ X34) @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.20/0.48          | (v3_relat_1 @ X34)
% 0.20/0.48          | ~ (v1_relat_1 @ X34))),
% 0.20/0.48      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (((~ (v1_relat_1 @ sk_A) | (v3_relat_1 @ sk_A)))
% 0.20/0.48         <= ((![X35 : $i]:
% 0.20/0.48                (((X35) = (k1_xboole_0))
% 0.20/0.48                 | ~ (r2_hidden @ X35 @ (k2_relat_1 @ sk_A)))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['41', '44'])).
% 0.20/0.48  thf('46', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (((v3_relat_1 @ sk_A))
% 0.20/0.48         <= ((![X35 : $i]:
% 0.20/0.48                (((X35) = (k1_xboole_0))
% 0.20/0.48                 | ~ (r2_hidden @ X35 @ (k2_relat_1 @ sk_A)))))),
% 0.20/0.48      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.48  thf('48', plain, ((~ (v3_relat_1 @ sk_A)) <= (~ ((v3_relat_1 @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (~
% 0.20/0.48       (![X35 : $i]:
% 0.20/0.48          (((X35) = (k1_xboole_0)) | ~ (r2_hidden @ X35 @ (k2_relat_1 @ sk_A)))) | 
% 0.20/0.48       ((v3_relat_1 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.48  thf('50', plain, ($false),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['1', '3', '26', '27', '49'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

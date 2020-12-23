%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3nZpxzrRg2

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 171 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :   20
%              Number of atoms          :  558 (1364 expanded)
%              Number of equality atoms :   46 ( 120 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t151_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t151_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( r1_xboole_0 @ X4 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X49 ) @ X50 )
      | ( ( k7_relat_1 @ X49 @ X50 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X45 @ X46 ) )
        = ( k9_relat_1 @ X45 @ X46 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X49 ) @ X50 )
      | ( ( k7_relat_1 @ X49 @ X50 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('18',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X45 @ X46 ) )
        = ( k9_relat_1 @ X45 @ X46 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('22',plain,
    ( ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = ( k9_relat_1 @ sk_B @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( ( k9_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
         != k1_xboole_0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( ( ( k9_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','26'])).

thf(t149_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X47: $i] :
      ( ( ( k9_relat_1 @ X47 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t149_relat_1])).

thf('29',plain,
    ( ! [X0: $i] :
        ~ ( v1_relat_1 @ X0 )
   <= ( ( ( k9_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','29'])).

thf('31',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','30'])).

thf('32',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf('33',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('34',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('35',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','30','34'])).

thf('36',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X45 @ X46 ) )
        = ( k9_relat_1 @ X45 @ X46 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('38',plain,(
    ! [X48: $i] :
      ( ( r1_tarski @ X48 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X48 ) @ ( k2_relat_1 @ X48 ) ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_tarski @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X4: $i] :
      ( r1_xboole_0 @ X4 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('44',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X34 @ X35 ) @ ( k2_zfmisc_1 @ X36 @ X37 ) )
      | ~ ( r1_xboole_0 @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('46',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r1_tarski @ ( k7_relat_1 @ sk_B @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['42','47','48'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('50',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k7_relat_1 @ X49 @ X50 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X49 ) @ X50 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['32','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3nZpxzrRg2
% 0.13/0.37  % Computer   : n014.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 19:52:37 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 100 iterations in 0.041s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(t151_relat_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ B ) =>
% 0.22/0.52       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.52         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( v1_relat_1 @ B ) =>
% 0.22/0.52          ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.52            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t151_relat_1])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.22/0.52        | ((k9_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.22/0.52         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.22/0.52       ~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.52  thf('4', plain, (![X4 : $i]: (r1_xboole_0 @ X4 @ k1_xboole_0)),
% 0.22/0.52      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.52  thf(t95_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ B ) =>
% 0.22/0.52       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.52         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X49 : $i, X50 : $i]:
% 0.22/0.52         (~ (r1_xboole_0 @ (k1_relat_1 @ X49) @ X50)
% 0.22/0.52          | ((k7_relat_1 @ X49 @ X50) = (k1_xboole_0))
% 0.22/0.52          | ~ (v1_relat_1 @ X49))),
% 0.22/0.52      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X0)
% 0.22/0.52          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.52  thf(dt_k7_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X43 : $i, X44 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X43) | (v1_relat_1 @ (k7_relat_1 @ X43 @ X44)))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v1_relat_1 @ k1_xboole_0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.52  thf('10', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '9'])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X0)
% 0.22/0.52          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.52  thf(t148_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ B ) =>
% 0.22/0.52       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X45 : $i, X46 : $i]:
% 0.22/0.52         (((k2_relat_1 @ (k7_relat_1 @ X45 @ X46)) = (k9_relat_1 @ X45 @ X46))
% 0.22/0.52          | ~ (v1_relat_1 @ X45))),
% 0.22/0.52      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.52          | ~ (v1_relat_1 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X0)
% 0.22/0.52          | ((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.22/0.52        | ((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.22/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.52      inference('split', [status(esa)], ['15'])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X49 : $i, X50 : $i]:
% 0.22/0.52         (~ (r1_xboole_0 @ (k1_relat_1 @ X49) @ X50)
% 0.22/0.52          | ((k7_relat_1 @ X49 @ X50) = (k1_xboole_0))
% 0.22/0.52          | ~ (v1_relat_1 @ X49))),
% 0.22/0.52      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (((~ (v1_relat_1 @ sk_B) | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.52  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.22/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X45 : $i, X46 : $i]:
% 0.22/0.52         (((k2_relat_1 @ (k7_relat_1 @ X45 @ X46)) = (k9_relat_1 @ X45 @ X46))
% 0.22/0.52          | ~ (v1_relat_1 @ X45))),
% 0.22/0.52      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (((((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ sk_B @ sk_A))
% 0.22/0.52         | ~ (v1_relat_1 @ sk_B)))
% 0.22/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      ((((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ sk_B @ sk_A)))
% 0.22/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      ((((k9_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.22/0.52         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.52         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.22/0.52             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          (((k9_relat_1 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 0.22/0.52           | ~ (v1_relat_1 @ X0)))
% 0.22/0.52         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.22/0.52             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['14', '26'])).
% 0.22/0.52  thf(t149_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (![X47 : $i]:
% 0.22/0.52         (((k9_relat_1 @ X47 @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.52          | ~ (v1_relat_1 @ X47))),
% 0.22/0.52      inference('cnf', [status(esa)], [t149_relat_1])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      ((![X0 : $i]: ~ (v1_relat_1 @ X0))
% 0.22/0.52         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.22/0.52             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.52      inference('clc', [status(thm)], ['27', '28'])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.22/0.52       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['10', '29'])).
% 0.22/0.52  thf('31', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['2', '30'])).
% 0.22/0.52  thf('32', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['1', '31'])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.22/0.52         <= ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.52      inference('split', [status(esa)], ['15'])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.22/0.52       ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.22/0.52      inference('split', [status(esa)], ['15'])).
% 0.22/0.52  thf('35', plain, ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['2', '30', '34'])).
% 0.22/0.52  thf('36', plain, (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['33', '35'])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X45 : $i, X46 : $i]:
% 0.22/0.52         (((k2_relat_1 @ (k7_relat_1 @ X45 @ X46)) = (k9_relat_1 @ X45 @ X46))
% 0.22/0.52          | ~ (v1_relat_1 @ X45))),
% 0.22/0.52      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.22/0.52  thf(t21_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( r1_tarski @
% 0.22/0.52         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X48 : $i]:
% 0.22/0.52         ((r1_tarski @ X48 @ 
% 0.22/0.52           (k2_zfmisc_1 @ (k1_relat_1 @ X48) @ (k2_relat_1 @ X48)))
% 0.22/0.52          | ~ (v1_relat_1 @ X48))),
% 0.22/0.52      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r1_tarski @ (k7_relat_1 @ X1 @ X0) @ 
% 0.22/0.52           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.22/0.52            (k9_relat_1 @ X1 @ X0)))
% 0.22/0.52          | ~ (v1_relat_1 @ X1)
% 0.22/0.52          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['37', '38'])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      (![X43 : $i, X44 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X43) | (v1_relat_1 @ (k7_relat_1 @ X43 @ X44)))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X1)
% 0.22/0.52          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ 
% 0.22/0.52             (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.22/0.52              (k9_relat_1 @ X1 @ X0))))),
% 0.22/0.52      inference('clc', [status(thm)], ['39', '40'])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (((r1_tarski @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.22/0.52         (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ k1_xboole_0))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.52      inference('sup+', [status(thm)], ['36', '41'])).
% 0.22/0.52  thf('43', plain, (![X4 : $i]: (r1_xboole_0 @ X4 @ k1_xboole_0)),
% 0.22/0.52      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.52  thf(t127_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.22/0.52       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ (k2_zfmisc_1 @ X34 @ X35) @ (k2_zfmisc_1 @ X36 @ X37))
% 0.22/0.52          | ~ (r1_xboole_0 @ X35 @ X37))),
% 0.22/0.52      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.22/0.52  thf('45', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ 
% 0.22/0.52          (k2_zfmisc_1 @ X1 @ k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.52  thf(t66_xboole_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.22/0.52       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.52  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('49', plain, ((r1_tarski @ (k7_relat_1 @ sk_B @ sk_A) @ k1_xboole_0)),
% 0.22/0.52      inference('demod', [status(thm)], ['42', '47', '48'])).
% 0.22/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.52  thf('50', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.52  thf(d10_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      (![X0 : $i, X2 : $i]:
% 0.22/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.52  thf('52', plain,
% 0.22/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['50', '51'])).
% 0.22/0.52  thf('53', plain, (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['49', '52'])).
% 0.22/0.52  thf('54', plain,
% 0.22/0.52      (![X49 : $i, X50 : $i]:
% 0.22/0.52         (((k7_relat_1 @ X49 @ X50) != (k1_xboole_0))
% 0.22/0.52          | (r1_xboole_0 @ (k1_relat_1 @ X49) @ X50)
% 0.22/0.52          | ~ (v1_relat_1 @ X49))),
% 0.22/0.52      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.22/0.52  thf('55', plain,
% 0.22/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_B)
% 0.22/0.52        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['53', '54'])).
% 0.22/0.52  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('57', plain,
% 0.22/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.52        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['55', '56'])).
% 0.22/0.52  thf('58', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.22/0.52      inference('simplify', [status(thm)], ['57'])).
% 0.22/0.52  thf('59', plain, ($false), inference('demod', [status(thm)], ['32', '58'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

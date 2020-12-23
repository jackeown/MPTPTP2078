%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0Z9TnwYW8L

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 100 expanded)
%              Number of leaves         :   23 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  512 ( 804 expanded)
%              Number of equality atoms :   52 (  82 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t95_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k7_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X46 @ X47 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X46 ) @ X47 ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X46 @ X47 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X46 ) @ X47 ) ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_xboole_0
      = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
   <= ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('12',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) )
   <= ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('19',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X46 @ X47 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X46 ) @ X47 ) ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('25',plain,(
    ! [X45: $i] :
      ( ( r1_tarski @ X45 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X1 ) @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X1 ) @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( r1_tarski @ ( k7_relat_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B_1 @ sk_A ) ) ) )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('30',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k2_zfmisc_1 @ X39 @ X40 )
        = k1_xboole_0 )
      | ( X39 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('31',plain,(
    ! [X40: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X40 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r1_tarski @ ( k7_relat_1 @ sk_B_1 @ sk_A ) @ k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['29','31','32'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k7_relat_1 @ sk_B_1 @ sk_A ) @ k1_xboole_0 ) )
      = ( k7_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('38',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_xboole_0
      = ( k7_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','17','18','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0Z9TnwYW8L
% 0.15/0.36  % Computer   : n024.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 14:02:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 80 iterations in 0.038s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.51  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(t95_relat_1, conjecture,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ B ) =>
% 0.22/0.51       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.51         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i]:
% 0.22/0.51        ( ( v1_relat_1 @ B ) =>
% 0.22/0.51          ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.51            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t95_relat_1])).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.22/0.51        | ((k7_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.22/0.51       ~ (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.22/0.51        | ((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.22/0.51         <= ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf(t90_relat_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ B ) =>
% 0.22/0.51       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.22/0.51         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (![X46 : $i, X47 : $i]:
% 0.22/0.51         (((k1_relat_1 @ (k7_relat_1 @ X46 @ X47))
% 0.22/0.51            = (k3_xboole_0 @ (k1_relat_1 @ X46) @ X47))
% 0.22/0.51          | ~ (v1_relat_1 @ X46))),
% 0.22/0.51      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.22/0.51  thf(t12_setfam_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (![X41 : $i, X42 : $i]:
% 0.22/0.51         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.22/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X46 : $i, X47 : $i]:
% 0.22/0.51         (((k1_relat_1 @ (k7_relat_1 @ X46 @ X47))
% 0.22/0.51            = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X46) @ X47)))
% 0.22/0.51          | ~ (v1_relat_1 @ X46))),
% 0.22/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (((((k1_relat_1 @ k1_xboole_0)
% 0.22/0.51           = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A)))
% 0.22/0.51         | ~ (v1_relat_1 @ sk_B_1)))
% 0.22/0.51         <= ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.51      inference('sup+', [status(thm)], ['3', '6'])).
% 0.22/0.51  thf(t60_relat_1, axiom,
% 0.22/0.51    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.51     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.51  thf('8', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.51  thf('9', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      ((((k1_xboole_0)
% 0.22/0.51          = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A))))
% 0.22/0.51         <= ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.51      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.22/0.51  thf(d7_xboole_0, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.22/0.51       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X0 : $i, X2 : $i]:
% 0.22/0.51         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.22/0.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X41 : $i, X42 : $i]:
% 0.22/0.51         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.22/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X0 : $i, X2 : $i]:
% 0.22/0.51         ((r1_xboole_0 @ X0 @ X2)
% 0.22/0.51          | ((k1_setfam_1 @ (k2_tarski @ X0 @ X2)) != (k1_xboole_0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.51         | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))
% 0.22/0.51         <= ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['10', '13'])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.22/0.51         <= ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.51      inference('simplify', [status(thm)], ['14'])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.22/0.51         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.22/0.51       ~ (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.22/0.51       (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.22/0.51         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (![X41 : $i, X42 : $i]:
% 0.22/0.51         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.22/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (((k1_setfam_1 @ (k2_tarski @ X0 @ X1)) = (k1_xboole_0))
% 0.22/0.51          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      ((((k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.22/0.51          = (k1_xboole_0)))
% 0.22/0.51         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['19', '22'])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X46 : $i, X47 : $i]:
% 0.22/0.51         (((k1_relat_1 @ (k7_relat_1 @ X46 @ X47))
% 0.22/0.51            = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X46) @ X47)))
% 0.22/0.51          | ~ (v1_relat_1 @ X46))),
% 0.22/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.51  thf(t21_relat_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ A ) =>
% 0.22/0.51       ( r1_tarski @
% 0.22/0.51         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      (![X45 : $i]:
% 0.22/0.51         ((r1_tarski @ X45 @ 
% 0.22/0.51           (k2_zfmisc_1 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45)))
% 0.22/0.51          | ~ (v1_relat_1 @ X45))),
% 0.22/0.51      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((r1_tarski @ (k7_relat_1 @ X1 @ X0) @ 
% 0.22/0.51           (k2_zfmisc_1 @ 
% 0.22/0.51            (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X1) @ X0)) @ 
% 0.22/0.51            (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.22/0.51          | ~ (v1_relat_1 @ X1)
% 0.22/0.51          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.51  thf(dt_k7_relat_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      (![X43 : $i, X44 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ X43) | (v1_relat_1 @ (k7_relat_1 @ X43 @ X44)))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.22/0.51  thf('28', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ X1)
% 0.22/0.51          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ 
% 0.22/0.51             (k2_zfmisc_1 @ 
% 0.22/0.51              (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X1) @ X0)) @ 
% 0.22/0.51              (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)))))),
% 0.22/0.51      inference('clc', [status(thm)], ['26', '27'])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      ((((r1_tarski @ (k7_relat_1 @ sk_B_1 @ sk_A) @ 
% 0.22/0.51          (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.22/0.51           (k2_relat_1 @ (k7_relat_1 @ sk_B_1 @ sk_A))))
% 0.22/0.51         | ~ (v1_relat_1 @ sk_B_1)))
% 0.22/0.51         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['23', '28'])).
% 0.22/0.51  thf(t113_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      (![X39 : $i, X40 : $i]:
% 0.22/0.51         (((k2_zfmisc_1 @ X39 @ X40) = (k1_xboole_0))
% 0.22/0.51          | ((X39) != (k1_xboole_0)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      (![X40 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X40) = (k1_xboole_0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['30'])).
% 0.22/0.51  thf('32', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      (((r1_tarski @ (k7_relat_1 @ sk_B_1 @ sk_A) @ k1_xboole_0))
% 0.22/0.51         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['29', '31', '32'])).
% 0.22/0.51  thf(t28_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i]:
% 0.22/0.51         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.22/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.51  thf('35', plain,
% 0.22/0.51      (![X41 : $i, X42 : $i]:
% 0.22/0.51         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.22/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i]:
% 0.22/0.51         (((k1_setfam_1 @ (k2_tarski @ X8 @ X9)) = (X8))
% 0.22/0.51          | ~ (r1_tarski @ X8 @ X9))),
% 0.22/0.51      inference('demod', [status(thm)], ['34', '35'])).
% 0.22/0.51  thf('37', plain,
% 0.22/0.51      ((((k1_setfam_1 @ 
% 0.22/0.51          (k2_tarski @ (k7_relat_1 @ sk_B_1 @ sk_A) @ k1_xboole_0))
% 0.22/0.51          = (k7_relat_1 @ sk_B_1 @ sk_A)))
% 0.22/0.51         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['33', '36'])).
% 0.22/0.51  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.51  thf('38', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 0.22/0.51      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.51  thf('39', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (((k1_setfam_1 @ (k2_tarski @ X0 @ X1)) = (k1_xboole_0))
% 0.22/0.51          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.51  thf('40', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.51  thf('41', plain,
% 0.22/0.51      ((((k1_xboole_0) = (k7_relat_1 @ sk_B_1 @ sk_A)))
% 0.22/0.51         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['37', '40'])).
% 0.22/0.51  thf('42', plain,
% 0.22/0.51      ((((k7_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.22/0.51         <= (~ (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('43', plain,
% 0.22/0.51      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.51         <= (~ (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 0.22/0.51             ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.51  thf('44', plain,
% 0.22/0.51      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.22/0.51       (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['43'])).
% 0.22/0.51  thf('45', plain, ($false),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['1', '17', '18', '44'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

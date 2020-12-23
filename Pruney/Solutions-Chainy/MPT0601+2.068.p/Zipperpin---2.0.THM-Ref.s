%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ngMAGu3eaD

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:50 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   72 (  93 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  524 ( 748 expanded)
%              Number of equality atoms :   35 (  55 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('0',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X43: $i] :
      ( ( ( k10_relat_1 @ X43 @ ( k2_relat_1 @ X43 ) )
        = ( k1_relat_1 @ X43 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X41 @ ( k10_relat_1 @ X42 @ X40 ) )
      | ( r2_hidden @ ( k4_tarski @ X41 @ ( sk_D @ X42 @ X40 @ X41 ) ) @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D @ X0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ) @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ) @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('12',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X46 @ X44 ) @ X45 )
      | ( r2_hidden @ X44 @ ( k11_relat_1 @ X45 @ X46 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('13',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','15'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('21',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33 != X35 )
      | ~ ( r2_hidden @ X33 @ ( k4_xboole_0 @ X34 @ ( k1_tarski @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('22',plain,(
    ! [X34: $i,X35: $i] :
      ~ ( r2_hidden @ X35 @ ( k4_xboole_0 @ X34 @ ( k1_tarski @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf('28',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('29',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('30',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X44 @ ( k11_relat_1 @ X45 @ X46 ) )
      | ( r2_hidden @ ( k4_tarski @ X46 @ X44 ) @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_B @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('32',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X47 @ X48 ) @ X49 )
      | ( r2_hidden @ X47 @ ( k1_relat_1 @ X49 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','27','28','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ngMAGu3eaD
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.60  % Solved by: fo/fo7.sh
% 0.37/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.60  % done 306 iterations in 0.165s
% 0.37/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.60  % SZS output start Refutation
% 0.37/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.37/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.60  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.37/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.37/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.60  thf(t205_relat_1, conjecture,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( v1_relat_1 @ B ) =>
% 0.37/0.60       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.37/0.60         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.37/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.60    (~( ![A:$i,B:$i]:
% 0.37/0.60        ( ( v1_relat_1 @ B ) =>
% 0.37/0.60          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.37/0.60            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.37/0.60    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.37/0.60  thf('0', plain,
% 0.37/0.60      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.37/0.60        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('1', plain,
% 0.37/0.60      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.37/0.60       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.37/0.60      inference('split', [status(esa)], ['0'])).
% 0.37/0.60  thf('2', plain,
% 0.37/0.60      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.37/0.60         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.60      inference('split', [status(esa)], ['0'])).
% 0.37/0.60  thf('3', plain,
% 0.37/0.60      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))
% 0.37/0.60        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('4', plain,
% 0.37/0.60      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.37/0.60         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.37/0.60      inference('split', [status(esa)], ['3'])).
% 0.37/0.60  thf(t169_relat_1, axiom,
% 0.37/0.60    (![A:$i]:
% 0.37/0.60     ( ( v1_relat_1 @ A ) =>
% 0.37/0.60       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.37/0.60  thf('5', plain,
% 0.37/0.60      (![X43 : $i]:
% 0.37/0.60         (((k10_relat_1 @ X43 @ (k2_relat_1 @ X43)) = (k1_relat_1 @ X43))
% 0.37/0.60          | ~ (v1_relat_1 @ X43))),
% 0.37/0.60      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.37/0.60  thf(t166_relat_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( v1_relat_1 @ C ) =>
% 0.37/0.60       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.37/0.60         ( ?[D:$i]:
% 0.37/0.60           ( ( r2_hidden @ D @ B ) & 
% 0.37/0.60             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.37/0.60             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.37/0.60  thf('6', plain,
% 0.37/0.60      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X41 @ (k10_relat_1 @ X42 @ X40))
% 0.37/0.60          | (r2_hidden @ (k4_tarski @ X41 @ (sk_D @ X42 @ X40 @ X41)) @ X42)
% 0.37/0.60          | ~ (v1_relat_1 @ X42))),
% 0.37/0.60      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.37/0.60  thf('7', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.37/0.60          | ~ (v1_relat_1 @ X0)
% 0.37/0.60          | ~ (v1_relat_1 @ X0)
% 0.37/0.60          | (r2_hidden @ 
% 0.37/0.60             (k4_tarski @ X1 @ (sk_D @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.60  thf('8', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((r2_hidden @ 
% 0.37/0.60           (k4_tarski @ X1 @ (sk_D @ X0 @ (k2_relat_1 @ X0) @ X1)) @ X0)
% 0.37/0.60          | ~ (v1_relat_1 @ X0)
% 0.37/0.60          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.37/0.60      inference('simplify', [status(thm)], ['7'])).
% 0.37/0.60  thf('9', plain,
% 0.37/0.60      (((~ (v1_relat_1 @ sk_B_1)
% 0.37/0.60         | (r2_hidden @ 
% 0.37/0.60            (k4_tarski @ sk_A @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A)) @ 
% 0.37/0.60            sk_B_1)))
% 0.37/0.60         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['4', '8'])).
% 0.37/0.60  thf('10', plain, ((v1_relat_1 @ sk_B_1)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('11', plain,
% 0.37/0.60      (((r2_hidden @ 
% 0.37/0.60         (k4_tarski @ sk_A @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A)) @ 
% 0.37/0.60         sk_B_1)) <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.37/0.60      inference('demod', [status(thm)], ['9', '10'])).
% 0.37/0.60  thf(t204_relat_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( v1_relat_1 @ C ) =>
% 0.37/0.60       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.37/0.60         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.37/0.60  thf('12', plain,
% 0.37/0.60      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.37/0.60         (~ (r2_hidden @ (k4_tarski @ X46 @ X44) @ X45)
% 0.37/0.60          | (r2_hidden @ X44 @ (k11_relat_1 @ X45 @ X46))
% 0.37/0.60          | ~ (v1_relat_1 @ X45))),
% 0.37/0.60      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.37/0.60  thf('13', plain,
% 0.37/0.60      (((~ (v1_relat_1 @ sk_B_1)
% 0.37/0.60         | (r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ 
% 0.37/0.60            (k11_relat_1 @ sk_B_1 @ sk_A))))
% 0.37/0.60         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.60  thf('14', plain, ((v1_relat_1 @ sk_B_1)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('15', plain,
% 0.37/0.60      (((r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ 
% 0.37/0.60         (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.37/0.60         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.37/0.60      inference('demod', [status(thm)], ['13', '14'])).
% 0.37/0.60  thf('16', plain,
% 0.37/0.60      (((r2_hidden @ (sk_D @ sk_B_1 @ (k2_relat_1 @ sk_B_1) @ sk_A) @ 
% 0.37/0.60         k1_xboole_0))
% 0.37/0.60         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.37/0.60             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.60      inference('sup+', [status(thm)], ['2', '15'])).
% 0.37/0.60  thf(idempotence_k3_xboole_0, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.37/0.60  thf('17', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.37/0.60  thf(t100_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.60  thf('18', plain,
% 0.37/0.60      (![X2 : $i, X3 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ X2 @ X3)
% 0.37/0.60           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.60  thf('19', plain,
% 0.37/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['17', '18'])).
% 0.37/0.60  thf(t69_enumset1, axiom,
% 0.37/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.60  thf('20', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.37/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.60  thf(t64_zfmisc_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.37/0.60       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.37/0.60  thf('21', plain,
% 0.37/0.60      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.37/0.60         (((X33) != (X35))
% 0.37/0.60          | ~ (r2_hidden @ X33 @ (k4_xboole_0 @ X34 @ (k1_tarski @ X35))))),
% 0.37/0.60      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.37/0.60  thf('22', plain,
% 0.37/0.60      (![X34 : $i, X35 : $i]:
% 0.37/0.60         ~ (r2_hidden @ X35 @ (k4_xboole_0 @ X34 @ (k1_tarski @ X35)))),
% 0.37/0.60      inference('simplify', [status(thm)], ['21'])).
% 0.37/0.60  thf('23', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['20', '22'])).
% 0.37/0.60  thf('24', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ~ (r2_hidden @ X0 @ 
% 0.37/0.60            (k5_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X0 @ X0)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['19', '23'])).
% 0.37/0.60  thf(t92_xboole_1, axiom,
% 0.37/0.60    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.60  thf('25', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.37/0.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.60  thf('26', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.37/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.37/0.60  thf('27', plain,
% 0.37/0.60      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.37/0.60       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['16', '26'])).
% 0.37/0.60  thf('28', plain,
% 0.37/0.60      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.37/0.60       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.37/0.60      inference('split', [status(esa)], ['3'])).
% 0.37/0.60  thf(t7_xboole_0, axiom,
% 0.37/0.60    (![A:$i]:
% 0.37/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.60          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.37/0.60  thf('29', plain,
% 0.37/0.60      (![X1 : $i]: (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 0.37/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.60  thf('30', plain,
% 0.37/0.60      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X44 @ (k11_relat_1 @ X45 @ X46))
% 0.37/0.60          | (r2_hidden @ (k4_tarski @ X46 @ X44) @ X45)
% 0.37/0.60          | ~ (v1_relat_1 @ X45))),
% 0.37/0.60      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.37/0.60  thf('31', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.37/0.60          | ~ (v1_relat_1 @ X1)
% 0.37/0.60          | (r2_hidden @ (k4_tarski @ X0 @ (sk_B @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.37/0.60             X1))),
% 0.37/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.60  thf(t20_relat_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( v1_relat_1 @ C ) =>
% 0.37/0.60       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.37/0.60         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.37/0.60           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.37/0.60  thf('32', plain,
% 0.37/0.60      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.37/0.60         (~ (r2_hidden @ (k4_tarski @ X47 @ X48) @ X49)
% 0.37/0.60          | (r2_hidden @ X47 @ (k1_relat_1 @ X49))
% 0.37/0.60          | ~ (v1_relat_1 @ X49))),
% 0.37/0.60      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.37/0.60  thf('33', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (~ (v1_relat_1 @ X0)
% 0.37/0.60          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.37/0.60          | ~ (v1_relat_1 @ X0)
% 0.37/0.60          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.60  thf('34', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.37/0.60          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.37/0.60          | ~ (v1_relat_1 @ X0))),
% 0.37/0.60      inference('simplify', [status(thm)], ['33'])).
% 0.37/0.60  thf('35', plain,
% 0.37/0.60      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.37/0.60         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.37/0.60      inference('split', [status(esa)], ['0'])).
% 0.37/0.60  thf('36', plain,
% 0.37/0.60      (((~ (v1_relat_1 @ sk_B_1)
% 0.37/0.60         | ((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))
% 0.37/0.60         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.60  thf('37', plain, ((v1_relat_1 @ sk_B_1)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('38', plain,
% 0.37/0.60      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.37/0.60         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.37/0.60      inference('demod', [status(thm)], ['36', '37'])).
% 0.37/0.60  thf('39', plain,
% 0.37/0.60      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.37/0.60         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.60      inference('split', [status(esa)], ['3'])).
% 0.37/0.60  thf('40', plain,
% 0.37/0.60      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.37/0.60         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 0.37/0.60             ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['38', '39'])).
% 0.37/0.60  thf('41', plain,
% 0.37/0.60      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.37/0.60       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.37/0.60      inference('simplify', [status(thm)], ['40'])).
% 0.37/0.60  thf('42', plain, ($false),
% 0.37/0.60      inference('sat_resolution*', [status(thm)], ['1', '27', '28', '41'])).
% 0.37/0.60  
% 0.37/0.60  % SZS output end Refutation
% 0.37/0.60  
% 0.37/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

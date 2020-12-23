%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j4XObHUs15

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:56 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 309 expanded)
%              Number of leaves         :   25 ( 107 expanded)
%              Depth                    :   20
%              Number of atoms          :  509 (2459 expanded)
%              Number of equality atoms :   45 ( 221 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t172_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k10_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t172_relat_1])).

thf('0',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X37: $i] :
      ( ( X37
        = ( k3_tarski @ X33 ) )
      | ( r2_hidden @ ( sk_D @ X37 @ X33 ) @ X33 )
      | ( r2_hidden @ ( sk_C @ X37 @ X33 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('5',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( X39 != X41 )
      | ~ ( r2_hidden @ X39 @ ( k4_xboole_0 @ X40 @ ( k1_tarski @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('6',plain,(
    ! [X40: $i,X41: $i] :
      ~ ( r2_hidden @ X41 @ ( k4_xboole_0 @ X40 @ ( k1_tarski @ X41 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('11',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X33: $i,X37: $i] :
      ( ( X37
        = ( k3_tarski @ X33 ) )
      | ( r2_hidden @ ( sk_D @ X37 @ X33 ) @ X33 )
      | ( r2_hidden @ ( sk_C @ X37 @ X33 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('14',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X52 @ ( k10_relat_1 @ X53 @ X51 ) )
      | ( r2_hidden @ ( k4_tarski @ X52 @ ( sk_D_3 @ X53 @ X51 @ X52 ) ) @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k3_tarski @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( sk_D_3 @ X1 @ X0 @ ( sk_D @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( X1
        = ( k3_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('18',plain,(
    ! [X47: $i] :
      ( ( v1_relat_1 @ X47 )
      | ( r2_hidden @ ( sk_B @ X47 ) @ X47 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('20',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k3_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k3_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('24',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X33: $i,X37: $i,X38: $i] :
      ( ( X37
        = ( k3_tarski @ X33 ) )
      | ~ ( r2_hidden @ ( sk_C @ X37 @ X33 ) @ X38 )
      | ~ ( r2_hidden @ X38 @ X33 )
      | ~ ( r2_hidden @ ( sk_C @ X37 @ X33 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k10_relat_1 @ k1_xboole_0 @ X1 ) ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ k1_xboole_0 @ X1 ) )
      | ( X0
        = ( k3_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k10_relat_1 @ k1_xboole_0 @ X1 ) ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ k1_xboole_0 @ X1 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ k1_xboole_0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k10_relat_1 @ k1_xboole_0 @ X1 ) ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ k1_xboole_0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ k1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X52 @ ( k10_relat_1 @ X53 @ X51 ) )
      | ( r2_hidden @ ( k4_tarski @ X52 @ ( sk_D_3 @ X53 @ X51 @ X52 ) ) @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ k1_xboole_0 @ ( sk_D_3 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ k1_xboole_0 @ ( sk_D_3 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j4XObHUs15
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:40:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.80/0.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.80/0.99  % Solved by: fo/fo7.sh
% 0.80/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/0.99  % done 544 iterations in 0.539s
% 0.80/0.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.80/0.99  % SZS output start Refutation
% 0.80/0.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.80/0.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.80/0.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.80/0.99  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.80/0.99  thf(sk_B_type, type, sk_B: $i > $i).
% 0.80/0.99  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.80/0.99  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.80/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.80/0.99  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.80/0.99  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 0.80/0.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.80/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.80/0.99  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.80/0.99  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.80/0.99  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.80/0.99  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.80/0.99  thf(t172_relat_1, conjecture,
% 0.80/0.99    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.80/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.80/0.99    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.80/0.99    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.80/0.99  thf('0', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.80/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.99  thf(d4_tarski, axiom,
% 0.80/0.99    (![A:$i,B:$i]:
% 0.80/0.99     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.80/0.99       ( ![C:$i]:
% 0.80/0.99         ( ( r2_hidden @ C @ B ) <=>
% 0.80/0.99           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.80/0.99  thf('1', plain,
% 0.80/0.99      (![X33 : $i, X37 : $i]:
% 0.80/0.99         (((X37) = (k3_tarski @ X33))
% 0.80/0.99          | (r2_hidden @ (sk_D @ X37 @ X33) @ X33)
% 0.80/0.99          | (r2_hidden @ (sk_C @ X37 @ X33) @ X37))),
% 0.80/0.99      inference('cnf', [status(esa)], [d4_tarski])).
% 0.80/0.99  thf(idempotence_k3_xboole_0, axiom,
% 0.80/0.99    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.80/0.99  thf('2', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.80/0.99      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.80/0.99  thf(t100_xboole_1, axiom,
% 0.80/0.99    (![A:$i,B:$i]:
% 0.80/0.99     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.80/0.99  thf('3', plain,
% 0.80/0.99      (![X1 : $i, X2 : $i]:
% 0.80/0.99         ((k4_xboole_0 @ X1 @ X2)
% 0.80/0.99           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.80/0.99      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.80/0.99  thf('4', plain,
% 0.80/0.99      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.80/0.99      inference('sup+', [status(thm)], ['2', '3'])).
% 0.80/0.99  thf(t64_zfmisc_1, axiom,
% 0.80/0.99    (![A:$i,B:$i,C:$i]:
% 0.80/0.99     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.80/0.99       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.80/0.99  thf('5', plain,
% 0.80/0.99      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.80/0.99         (((X39) != (X41))
% 0.80/0.99          | ~ (r2_hidden @ X39 @ (k4_xboole_0 @ X40 @ (k1_tarski @ X41))))),
% 0.80/0.99      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.80/0.99  thf('6', plain,
% 0.80/0.99      (![X40 : $i, X41 : $i]:
% 0.80/0.99         ~ (r2_hidden @ X41 @ (k4_xboole_0 @ X40 @ (k1_tarski @ X41)))),
% 0.80/0.99      inference('simplify', [status(thm)], ['5'])).
% 0.80/0.99  thf('7', plain,
% 0.80/0.99      (![X0 : $i]:
% 0.80/0.99         ~ (r2_hidden @ X0 @ 
% 0.80/0.99            (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.80/0.99      inference('sup-', [status(thm)], ['4', '6'])).
% 0.80/0.99  thf(t92_xboole_1, axiom,
% 0.80/0.99    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.80/0.99  thf('8', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ X3) = (k1_xboole_0))),
% 0.80/0.99      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.80/0.99  thf('9', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.80/0.99      inference('demod', [status(thm)], ['7', '8'])).
% 0.80/0.99  thf('10', plain,
% 0.80/0.99      (![X0 : $i]:
% 0.80/0.99         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.80/0.99          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 0.80/0.99      inference('sup-', [status(thm)], ['1', '9'])).
% 0.80/0.99  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.80/0.99  thf('11', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/0.99      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.80/0.99  thf('12', plain,
% 0.80/0.99      (![X0 : $i]:
% 0.80/0.99         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.80/0.99      inference('demod', [status(thm)], ['10', '11'])).
% 0.80/0.99  thf('13', plain,
% 0.80/0.99      (![X33 : $i, X37 : $i]:
% 0.80/0.99         (((X37) = (k3_tarski @ X33))
% 0.80/0.99          | (r2_hidden @ (sk_D @ X37 @ X33) @ X33)
% 0.80/0.99          | (r2_hidden @ (sk_C @ X37 @ X33) @ X37))),
% 0.80/0.99      inference('cnf', [status(esa)], [d4_tarski])).
% 0.80/0.99  thf(t166_relat_1, axiom,
% 0.80/0.99    (![A:$i,B:$i,C:$i]:
% 0.80/0.99     ( ( v1_relat_1 @ C ) =>
% 0.80/0.99       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.80/0.99         ( ?[D:$i]:
% 0.80/0.99           ( ( r2_hidden @ D @ B ) & 
% 0.80/0.99             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.80/0.99             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.80/0.99  thf('14', plain,
% 0.80/0.99      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.80/0.99         (~ (r2_hidden @ X52 @ (k10_relat_1 @ X53 @ X51))
% 0.80/0.99          | (r2_hidden @ (k4_tarski @ X52 @ (sk_D_3 @ X53 @ X51 @ X52)) @ X53)
% 0.80/0.99          | ~ (v1_relat_1 @ X53))),
% 0.80/0.99      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.80/0.99  thf('15', plain,
% 0.80/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/0.99         ((r2_hidden @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)) @ X2)
% 0.80/0.99          | ((X2) = (k3_tarski @ (k10_relat_1 @ X1 @ X0)))
% 0.80/0.99          | ~ (v1_relat_1 @ X1)
% 0.80/0.99          | (r2_hidden @ 
% 0.80/0.99             (k4_tarski @ (sk_D @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.80/0.99              (sk_D_3 @ X1 @ X0 @ (sk_D @ X2 @ (k10_relat_1 @ X1 @ X0)))) @ 
% 0.80/0.99             X1))),
% 0.80/0.99      inference('sup-', [status(thm)], ['13', '14'])).
% 0.80/0.99  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.80/0.99      inference('demod', [status(thm)], ['7', '8'])).
% 0.80/0.99  thf('17', plain,
% 0.80/0.99      (![X0 : $i, X1 : $i]:
% 0.80/0.99         (~ (v1_relat_1 @ k1_xboole_0)
% 0.80/0.99          | ((X1) = (k3_tarski @ (k10_relat_1 @ k1_xboole_0 @ X0)))
% 0.80/0.99          | (r2_hidden @ (sk_C @ X1 @ (k10_relat_1 @ k1_xboole_0 @ X0)) @ X1))),
% 0.80/0.99      inference('sup-', [status(thm)], ['15', '16'])).
% 0.80/0.99  thf(d1_relat_1, axiom,
% 0.80/0.99    (![A:$i]:
% 0.80/0.99     ( ( v1_relat_1 @ A ) <=>
% 0.80/0.99       ( ![B:$i]:
% 0.80/0.99         ( ~( ( r2_hidden @ B @ A ) & 
% 0.80/0.99              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.80/0.99  thf('18', plain,
% 0.80/0.99      (![X47 : $i]: ((v1_relat_1 @ X47) | (r2_hidden @ (sk_B @ X47) @ X47))),
% 0.80/0.99      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.80/0.99  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.80/0.99      inference('demod', [status(thm)], ['7', '8'])).
% 0.80/0.99  thf('20', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.80/0.99      inference('sup-', [status(thm)], ['18', '19'])).
% 0.80/0.99  thf('21', plain,
% 0.80/0.99      (![X0 : $i, X1 : $i]:
% 0.80/0.99         (((X1) = (k3_tarski @ (k10_relat_1 @ k1_xboole_0 @ X0)))
% 0.80/0.99          | (r2_hidden @ (sk_C @ X1 @ (k10_relat_1 @ k1_xboole_0 @ X0)) @ X1))),
% 0.80/0.99      inference('demod', [status(thm)], ['17', '20'])).
% 0.80/0.99  thf('22', plain,
% 0.80/0.99      (![X0 : $i, X1 : $i]:
% 0.80/0.99         (((X1) = (k3_tarski @ (k10_relat_1 @ k1_xboole_0 @ X0)))
% 0.80/0.99          | (r2_hidden @ (sk_C @ X1 @ (k10_relat_1 @ k1_xboole_0 @ X0)) @ X1))),
% 0.80/0.99      inference('demod', [status(thm)], ['17', '20'])).
% 0.80/0.99  thf('23', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.80/0.99      inference('demod', [status(thm)], ['7', '8'])).
% 0.80/0.99  thf('24', plain,
% 0.80/0.99      (![X0 : $i]:
% 0.80/0.99         ((k1_xboole_0) = (k3_tarski @ (k10_relat_1 @ k1_xboole_0 @ X0)))),
% 0.80/0.99      inference('sup-', [status(thm)], ['22', '23'])).
% 0.80/0.99  thf('25', plain,
% 0.80/0.99      (![X0 : $i, X1 : $i]:
% 0.80/0.99         (((X1) = (k1_xboole_0))
% 0.80/0.99          | (r2_hidden @ (sk_C @ X1 @ (k10_relat_1 @ k1_xboole_0 @ X0)) @ X1))),
% 0.80/0.99      inference('demod', [status(thm)], ['21', '24'])).
% 0.80/0.99  thf('26', plain,
% 0.80/0.99      (![X33 : $i, X37 : $i, X38 : $i]:
% 0.80/0.99         (((X37) = (k3_tarski @ X33))
% 0.80/0.99          | ~ (r2_hidden @ (sk_C @ X37 @ X33) @ X38)
% 0.80/0.99          | ~ (r2_hidden @ X38 @ X33)
% 0.80/0.99          | ~ (r2_hidden @ (sk_C @ X37 @ X33) @ X37))),
% 0.80/0.99      inference('cnf', [status(esa)], [d4_tarski])).
% 0.80/0.99  thf('27', plain,
% 0.80/0.99      (![X0 : $i, X1 : $i]:
% 0.80/0.99         (((X0) = (k1_xboole_0))
% 0.80/0.99          | ~ (r2_hidden @ (sk_C @ X0 @ (k10_relat_1 @ k1_xboole_0 @ X1)) @ X0)
% 0.80/0.99          | ~ (r2_hidden @ X0 @ (k10_relat_1 @ k1_xboole_0 @ X1))
% 0.80/0.99          | ((X0) = (k3_tarski @ (k10_relat_1 @ k1_xboole_0 @ X1))))),
% 0.80/0.99      inference('sup-', [status(thm)], ['25', '26'])).
% 0.80/0.99  thf('28', plain,
% 0.80/0.99      (![X0 : $i]:
% 0.80/0.99         ((k1_xboole_0) = (k3_tarski @ (k10_relat_1 @ k1_xboole_0 @ X0)))),
% 0.80/0.99      inference('sup-', [status(thm)], ['22', '23'])).
% 0.80/0.99  thf('29', plain,
% 0.80/0.99      (![X0 : $i, X1 : $i]:
% 0.80/0.99         (((X0) = (k1_xboole_0))
% 0.80/0.99          | ~ (r2_hidden @ (sk_C @ X0 @ (k10_relat_1 @ k1_xboole_0 @ X1)) @ X0)
% 0.80/0.99          | ~ (r2_hidden @ X0 @ (k10_relat_1 @ k1_xboole_0 @ X1))
% 0.80/0.99          | ((X0) = (k1_xboole_0)))),
% 0.80/0.99      inference('demod', [status(thm)], ['27', '28'])).
% 0.80/0.99  thf('30', plain,
% 0.80/0.99      (![X0 : $i, X1 : $i]:
% 0.80/0.99         (~ (r2_hidden @ X0 @ (k10_relat_1 @ k1_xboole_0 @ X1))
% 0.80/0.99          | ~ (r2_hidden @ (sk_C @ X0 @ (k10_relat_1 @ k1_xboole_0 @ X1)) @ X0)
% 0.80/0.99          | ((X0) = (k1_xboole_0)))),
% 0.80/0.99      inference('simplify', [status(thm)], ['29'])).
% 0.80/0.99  thf('31', plain,
% 0.80/0.99      (![X0 : $i, X1 : $i]:
% 0.80/0.99         (((X1) = (k1_xboole_0))
% 0.80/0.99          | (r2_hidden @ (sk_C @ X1 @ (k10_relat_1 @ k1_xboole_0 @ X0)) @ X1))),
% 0.80/0.99      inference('demod', [status(thm)], ['21', '24'])).
% 0.80/0.99  thf('32', plain,
% 0.80/0.99      (![X0 : $i, X1 : $i]:
% 0.80/0.99         (((X0) = (k1_xboole_0))
% 0.80/0.99          | ~ (r2_hidden @ X0 @ (k10_relat_1 @ k1_xboole_0 @ X1)))),
% 0.80/0.99      inference('clc', [status(thm)], ['30', '31'])).
% 0.80/0.99  thf('33', plain,
% 0.80/0.99      (![X0 : $i]:
% 0.80/0.99         (((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.80/0.99          | ((sk_C @ (k10_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.80/0.99              = (k1_xboole_0)))),
% 0.80/0.99      inference('sup-', [status(thm)], ['12', '32'])).
% 0.80/0.99  thf('34', plain,
% 0.80/0.99      (![X0 : $i]:
% 0.80/0.99         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.80/0.99      inference('demod', [status(thm)], ['10', '11'])).
% 0.80/0.99  thf('35', plain,
% 0.80/0.99      (![X0 : $i]:
% 0.80/0.99         ((r2_hidden @ k1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0))
% 0.80/0.99          | ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.80/0.99          | ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.80/0.99      inference('sup+', [status(thm)], ['33', '34'])).
% 0.80/0.99  thf('36', plain,
% 0.80/0.99      (![X0 : $i]:
% 0.80/0.99         (((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.80/0.99          | (r2_hidden @ k1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0)))),
% 0.80/0.99      inference('simplify', [status(thm)], ['35'])).
% 0.80/0.99  thf('37', plain,
% 0.80/0.99      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.80/0.99         (~ (r2_hidden @ X52 @ (k10_relat_1 @ X53 @ X51))
% 0.80/0.99          | (r2_hidden @ (k4_tarski @ X52 @ (sk_D_3 @ X53 @ X51 @ X52)) @ X53)
% 0.80/0.99          | ~ (v1_relat_1 @ X53))),
% 0.80/0.99      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.80/1.00  thf('38', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.80/1.00          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.80/1.00          | (r2_hidden @ 
% 0.80/1.00             (k4_tarski @ k1_xboole_0 @ 
% 0.80/1.00              (sk_D_3 @ k1_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.80/1.00             k1_xboole_0))),
% 0.80/1.00      inference('sup-', [status(thm)], ['36', '37'])).
% 0.80/1.00  thf('39', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.80/1.00      inference('sup-', [status(thm)], ['18', '19'])).
% 0.80/1.00  thf('40', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         (((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.80/1.00          | (r2_hidden @ 
% 0.80/1.00             (k4_tarski @ k1_xboole_0 @ 
% 0.80/1.00              (sk_D_3 @ k1_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.80/1.00             k1_xboole_0))),
% 0.80/1.00      inference('demod', [status(thm)], ['38', '39'])).
% 0.80/1.00  thf('41', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.80/1.00      inference('demod', [status(thm)], ['7', '8'])).
% 0.80/1.00  thf('42', plain,
% 0.80/1.00      (![X0 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.80/1.00      inference('clc', [status(thm)], ['40', '41'])).
% 0.80/1.00  thf('43', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.80/1.00      inference('demod', [status(thm)], ['0', '42'])).
% 0.80/1.00  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 0.80/1.00  
% 0.80/1.00  % SZS output end Refutation
% 0.80/1.00  
% 0.80/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

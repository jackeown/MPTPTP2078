%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aW3eCqvmu0

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:42 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 207 expanded)
%              Number of leaves         :   27 (  65 expanded)
%              Depth                    :   22
%              Number of atoms          :  584 (1826 expanded)
%              Number of equality atoms :   43 ( 161 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('5',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k11_relat_1 @ X35 @ X36 )
        = ( k9_relat_1 @ X35 @ ( k1_tarski @ X36 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('7',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X29: $i,X31: $i,X32: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X29 @ X31 ) @ X32 )
      | ~ ( r2_hidden @ X31 @ X32 )
      | ~ ( r2_hidden @ X29 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_2 ) )
        | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t152_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X49: $i,X50: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X50 )
      | ~ ( r1_tarski @ X49 @ ( k1_relat_1 @ X50 ) )
      | ( ( k9_relat_1 @ X50 @ X49 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t152_relat_1])).

thf('14',plain,
    ( ( ( ( k9_relat_1 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_2 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( ( k9_relat_1 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
       != k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('18',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X33 ) @ X34 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k9_relat_1 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_2 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['5','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
      & ( ( k11_relat_1 @ sk_B_2 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
    | ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
    | ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['3','25','26'])).

thf('28',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(simpl_trail,[status(thm)],['1','27'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('29',plain,(
    ! [X39: $i] :
      ( ( v1_relat_1 @ X39 )
      | ( r2_hidden @ ( sk_B @ X39 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('30',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X51 @ ( k11_relat_1 @ X52 @ X53 ) )
      | ( r2_hidden @ ( k4_tarski @ X53 @ X51 ) @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_B @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('32',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X42 @ X43 ) @ X44 )
      | ( r2_hidden @ X42 @ X45 )
      | ( X45
       != ( k1_relat_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('33',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( r2_hidden @ X42 @ ( k1_relat_1 @ X44 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X42 @ X43 ) @ X44 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k11_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(simpl_trail,[status(thm)],['1','27'])).

thf('36',plain,
    ( ( v1_relat_1 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_relat_1 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X54: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X54 ) @ ( sk_C_2 @ X54 ) ) @ X54 )
      | ( X54 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('40',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X51 @ ( k11_relat_1 @ X52 @ X53 ) )
      | ( r2_hidden @ ( k4_tarski @ X53 @ X51 ) @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k4_tarski @ ( sk_B_1 @ ( k11_relat_1 @ X1 @ X0 ) ) @ ( sk_C_2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k4_tarski @ ( sk_B_1 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) @ ( sk_C_2 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) ) ) @ sk_B_2 )
    | ~ ( v1_relat_1 @ sk_B_2 )
    | ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k4_tarski @ ( sk_B_1 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) @ ( sk_C_2 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) ) ) @ sk_B_2 )
    | ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('46',plain,(
    ( k11_relat_1 @ sk_B_2 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','25'])).

thf('47',plain,(
    ( k11_relat_1 @ sk_B_2 @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['45','46'])).

thf('48',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k4_tarski @ ( sk_B_1 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) @ ( sk_C_2 @ ( k11_relat_1 @ sk_B_2 @ sk_A ) ) ) ) @ sk_B_2 ),
    inference('simplify_reflect-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( r2_hidden @ X42 @ ( k1_relat_1 @ X44 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X42 @ X43 ) @ X44 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('50',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['28','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aW3eCqvmu0
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:51:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 153 iterations in 0.095s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.38/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.56  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.38/0.56  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.38/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(t205_relat_1, conjecture,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ B ) =>
% 0.38/0.56       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.38/0.56         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i,B:$i]:
% 0.38/0.56        ( ( v1_relat_1 @ B ) =>
% 0.38/0.56          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.38/0.56            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.38/0.56  thf('0', plain,
% 0.38/0.56      ((((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))
% 0.38/0.56        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('1', plain,
% 0.38/0.56      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))
% 0.38/0.56         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.38/0.56      inference('split', [status(esa)], ['0'])).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      ((((k11_relat_1 @ sk_B_2 @ sk_A) != (k1_xboole_0))
% 0.38/0.56        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      (~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))) | 
% 0.38/0.56       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.38/0.56      inference('split', [status(esa)], ['2'])).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      ((((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))
% 0.38/0.56         <= ((((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('split', [status(esa)], ['0'])).
% 0.38/0.56  thf(d16_relat_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ A ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (![X35 : $i, X36 : $i]:
% 0.38/0.56         (((k11_relat_1 @ X35 @ X36) = (k9_relat_1 @ X35 @ (k1_tarski @ X36)))
% 0.38/0.56          | ~ (v1_relat_1 @ X35))),
% 0.38/0.56      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))
% 0.38/0.56         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.38/0.56      inference('split', [status(esa)], ['2'])).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))
% 0.38/0.56         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.38/0.56      inference('split', [status(esa)], ['2'])).
% 0.38/0.56  thf(t38_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.38/0.56       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      (![X29 : $i, X31 : $i, X32 : $i]:
% 0.38/0.56         ((r1_tarski @ (k2_tarski @ X29 @ X31) @ X32)
% 0.38/0.56          | ~ (r2_hidden @ X31 @ X32)
% 0.38/0.56          | ~ (r2_hidden @ X29 @ X32))),
% 0.38/0.56      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_2))
% 0.38/0.56           | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ (k1_relat_1 @ sk_B_2))))
% 0.38/0.56         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      (((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ (k1_relat_1 @ sk_B_2)))
% 0.38/0.56         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['6', '9'])).
% 0.38/0.56  thf(t69_enumset1, axiom,
% 0.38/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.38/0.56  thf('11', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_B_2)))
% 0.38/0.56         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.38/0.56      inference('demod', [status(thm)], ['10', '11'])).
% 0.38/0.56  thf(t152_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ B ) =>
% 0.38/0.56       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.56            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.38/0.56            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      (![X49 : $i, X50 : $i]:
% 0.38/0.56         (((X49) = (k1_xboole_0))
% 0.38/0.56          | ~ (v1_relat_1 @ X50)
% 0.38/0.56          | ~ (r1_tarski @ X49 @ (k1_relat_1 @ X50))
% 0.38/0.56          | ((k9_relat_1 @ X50 @ X49) != (k1_xboole_0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t152_relat_1])).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      (((((k9_relat_1 @ sk_B_2 @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.38/0.56         | ~ (v1_relat_1 @ sk_B_2)
% 0.38/0.56         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.38/0.56         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.56  thf('15', plain, ((v1_relat_1 @ sk_B_2)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      (((((k9_relat_1 @ sk_B_2 @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.38/0.56         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.38/0.56         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.38/0.56      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.56  thf(t1_boole, axiom,
% 0.38/0.56    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.56  thf('17', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.56      inference('cnf', [status(esa)], [t1_boole])).
% 0.38/0.56  thf(t49_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      (![X33 : $i, X34 : $i]:
% 0.38/0.56         ((k2_xboole_0 @ (k1_tarski @ X33) @ X34) != (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.38/0.56  thf('19', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      ((((k9_relat_1 @ sk_B_2 @ (k1_tarski @ sk_A)) != (k1_xboole_0)))
% 0.38/0.56         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['16', '19'])).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      (((((k11_relat_1 @ sk_B_2 @ sk_A) != (k1_xboole_0))
% 0.38/0.56         | ~ (v1_relat_1 @ sk_B_2)))
% 0.38/0.56         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['5', '20'])).
% 0.38/0.56  thf('22', plain, ((v1_relat_1 @ sk_B_2)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      ((((k11_relat_1 @ sk_B_2 @ sk_A) != (k1_xboole_0)))
% 0.38/0.56         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.38/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.38/0.56         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))) & 
% 0.38/0.56             (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['4', '23'])).
% 0.38/0.56  thf('25', plain,
% 0.38/0.56      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))) | 
% 0.38/0.56       ~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['24'])).
% 0.38/0.56  thf('26', plain,
% 0.38/0.56      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))) | 
% 0.38/0.56       (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.38/0.56      inference('split', [status(esa)], ['0'])).
% 0.38/0.56  thf('27', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)], ['3', '25', '26'])).
% 0.38/0.56  thf('28', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['1', '27'])).
% 0.38/0.56  thf(d1_relat_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ A ) <=>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ~( ( r2_hidden @ B @ A ) & 
% 0.38/0.56              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.38/0.56  thf('29', plain,
% 0.38/0.56      (![X39 : $i]: ((v1_relat_1 @ X39) | (r2_hidden @ (sk_B @ X39) @ X39))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.38/0.56  thf(t204_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ C ) =>
% 0.38/0.56       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.38/0.56         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.38/0.56  thf('30', plain,
% 0.38/0.56      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X51 @ (k11_relat_1 @ X52 @ X53))
% 0.38/0.56          | (r2_hidden @ (k4_tarski @ X53 @ X51) @ X52)
% 0.38/0.56          | ~ (v1_relat_1 @ X52))),
% 0.38/0.56      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((v1_relat_1 @ (k11_relat_1 @ X1 @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | (r2_hidden @ (k4_tarski @ X0 @ (sk_B @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.38/0.56             X1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.56  thf(d4_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.38/0.56       ( ![C:$i]:
% 0.38/0.56         ( ( r2_hidden @ C @ B ) <=>
% 0.38/0.56           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.38/0.56  thf('32', plain,
% 0.38/0.56      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.38/0.56         (~ (r2_hidden @ (k4_tarski @ X42 @ X43) @ X44)
% 0.38/0.56          | (r2_hidden @ X42 @ X45)
% 0.38/0.56          | ((X45) != (k1_relat_1 @ X44)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.38/0.56  thf('33', plain,
% 0.38/0.56      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.38/0.56         ((r2_hidden @ X42 @ (k1_relat_1 @ X44))
% 0.38/0.56          | ~ (r2_hidden @ (k4_tarski @ X42 @ X43) @ X44))),
% 0.38/0.56      inference('simplify', [status(thm)], ['32'])).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0)
% 0.38/0.56          | (v1_relat_1 @ (k11_relat_1 @ X0 @ X1))
% 0.38/0.56          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['31', '33'])).
% 0.38/0.56  thf('35', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['1', '27'])).
% 0.38/0.56  thf('36', plain,
% 0.38/0.56      (((v1_relat_1 @ (k11_relat_1 @ sk_B_2 @ sk_A)) | ~ (v1_relat_1 @ sk_B_2))),
% 0.38/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.56  thf('37', plain, ((v1_relat_1 @ sk_B_2)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('38', plain, ((v1_relat_1 @ (k11_relat_1 @ sk_B_2 @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['36', '37'])).
% 0.38/0.56  thf(t56_relat_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ A ) =>
% 0.38/0.56       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.38/0.56         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.56  thf('39', plain,
% 0.38/0.56      (![X54 : $i]:
% 0.38/0.56         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X54) @ (sk_C_2 @ X54)) @ X54)
% 0.38/0.56          | ((X54) = (k1_xboole_0))
% 0.38/0.56          | ~ (v1_relat_1 @ X54))),
% 0.38/0.56      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.38/0.56  thf('40', plain,
% 0.38/0.56      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X51 @ (k11_relat_1 @ X52 @ X53))
% 0.38/0.56          | (r2_hidden @ (k4_tarski @ X53 @ X51) @ X52)
% 0.38/0.56          | ~ (v1_relat_1 @ X52))),
% 0.38/0.56      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.38/0.56  thf('41', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ (k11_relat_1 @ X1 @ X0))
% 0.38/0.56          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | (r2_hidden @ 
% 0.38/0.56             (k4_tarski @ X0 @ 
% 0.38/0.56              (k4_tarski @ (sk_B_1 @ (k11_relat_1 @ X1 @ X0)) @ 
% 0.38/0.56               (sk_C_2 @ (k11_relat_1 @ X1 @ X0)))) @ 
% 0.38/0.56             X1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.56  thf('42', plain,
% 0.38/0.56      (((r2_hidden @ 
% 0.38/0.56         (k4_tarski @ sk_A @ 
% 0.38/0.56          (k4_tarski @ (sk_B_1 @ (k11_relat_1 @ sk_B_2 @ sk_A)) @ 
% 0.38/0.56           (sk_C_2 @ (k11_relat_1 @ sk_B_2 @ sk_A)))) @ 
% 0.38/0.56         sk_B_2)
% 0.38/0.56        | ~ (v1_relat_1 @ sk_B_2)
% 0.38/0.56        | ((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['38', '41'])).
% 0.38/0.56  thf('43', plain, ((v1_relat_1 @ sk_B_2)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('44', plain,
% 0.38/0.56      (((r2_hidden @ 
% 0.38/0.56         (k4_tarski @ sk_A @ 
% 0.38/0.56          (k4_tarski @ (sk_B_1 @ (k11_relat_1 @ sk_B_2 @ sk_A)) @ 
% 0.38/0.56           (sk_C_2 @ (k11_relat_1 @ sk_B_2 @ sk_A)))) @ 
% 0.38/0.56         sk_B_2)
% 0.38/0.56        | ((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.38/0.56      inference('demod', [status(thm)], ['42', '43'])).
% 0.38/0.56  thf('45', plain,
% 0.38/0.56      ((((k11_relat_1 @ sk_B_2 @ sk_A) != (k1_xboole_0)))
% 0.38/0.56         <= (~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('split', [status(esa)], ['2'])).
% 0.38/0.56  thf('46', plain, (~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)], ['3', '25'])).
% 0.38/0.56  thf('47', plain, (((k11_relat_1 @ sk_B_2 @ sk_A) != (k1_xboole_0))),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['45', '46'])).
% 0.38/0.56  thf('48', plain,
% 0.38/0.56      ((r2_hidden @ 
% 0.38/0.56        (k4_tarski @ sk_A @ 
% 0.38/0.56         (k4_tarski @ (sk_B_1 @ (k11_relat_1 @ sk_B_2 @ sk_A)) @ 
% 0.38/0.56          (sk_C_2 @ (k11_relat_1 @ sk_B_2 @ sk_A)))) @ 
% 0.38/0.56        sk_B_2)),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['44', '47'])).
% 0.38/0.56  thf('49', plain,
% 0.38/0.56      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.38/0.56         ((r2_hidden @ X42 @ (k1_relat_1 @ X44))
% 0.38/0.56          | ~ (r2_hidden @ (k4_tarski @ X42 @ X43) @ X44))),
% 0.38/0.56      inference('simplify', [status(thm)], ['32'])).
% 0.38/0.56  thf('50', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))),
% 0.38/0.56      inference('sup-', [status(thm)], ['48', '49'])).
% 0.38/0.56  thf('51', plain, ($false), inference('demod', [status(thm)], ['28', '50'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

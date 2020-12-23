%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zyn7bEBaZR

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 253 expanded)
%              Number of leaves         :   31 (  92 expanded)
%              Depth                    :   18
%              Number of atoms          :  542 (1820 expanded)
%              Number of equality atoms :   70 ( 245 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('0',plain,(
    ! [X50: $i,X53: $i] :
      ( ( X53
        = ( k2_relat_1 @ X50 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X53 @ X50 ) @ ( sk_C_1 @ X53 @ X50 ) ) @ X50 )
      | ( r2_hidden @ ( sk_C_1 @ X53 @ X50 ) @ X53 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X33: $i,X35: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X33 ) @ X35 )
      | ~ ( r2_hidden @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ ( k4_tarski @ ( sk_D_1 @ X1 @ X0 ) @ ( sk_C_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( ( k1_tarski @ ( k4_tarski @ ( sk_D_1 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('5',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X39 != X38 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X39 ) @ ( k1_tarski @ X38 ) )
       != ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('6',plain,(
    ! [X38: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X38 ) )
     != ( k1_tarski @ X38 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X36 ) @ ( k2_tarski @ X36 @ X37 ) )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ ( k1_tarski @ X0 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X38: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X38 ) ) ),
    inference(demod,[status(thm)],['6','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['4','20'])).

thf('22',plain,(
    ! [X33: $i,X35: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X33 ) @ X35 )
      | ~ ( r2_hidden @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('25',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ( ( k1_tarski @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X38: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X38 ) ) ),
    inference(demod,[status(thm)],['6','19'])).

thf('27',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) )).

thf('29',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X55 ) @ ( k2_relat_1 @ X55 ) )
      | ~ ( r2_hidden @ X56 @ ( k1_relat_1 @ X55 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t18_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X33: $i,X35: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X33 ) @ X35 )
      | ~ ( r2_hidden @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C_2 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 ) ) @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('34',plain,(
    ! [X45: $i] :
      ( ( v1_relat_1 @ X45 )
      | ( r2_hidden @ ( sk_B_1 @ X45 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('35',plain,(
    ! [X33: $i,X35: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X33 ) @ X35 )
      | ~ ( r2_hidden @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('38',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_tarski @ ( sk_B_1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X38: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X38 ) ) ),
    inference(demod,[status(thm)],['6','19'])).

thf('40',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 ) ) @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','40'])).

thf(t60_relat_1,conjecture,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      & ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_relat_1])).

thf('42',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('45',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('49',plain,(
    ( k1_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['47','48'])).

thf('50',plain,(
    ( k1_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['43','49'])).

thf('51',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 ) ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['41','50'])).

thf('52',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('53',plain,
    ( ( k1_tarski @ ( sk_C_2 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X38: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X38 ) ) ),
    inference(demod,[status(thm)],['6','19'])).

thf('55',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference(simplify,[status(thm)],['55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zyn7bEBaZR
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:35:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 346 iterations in 0.111s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.57  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.21/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.57  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.57  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.57  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.57  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.57  thf(d5_relat_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.21/0.57       ( ![C:$i]:
% 0.21/0.57         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.57           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      (![X50 : $i, X53 : $i]:
% 0.21/0.57         (((X53) = (k2_relat_1 @ X50))
% 0.21/0.57          | (r2_hidden @ 
% 0.21/0.57             (k4_tarski @ (sk_D_1 @ X53 @ X50) @ (sk_C_1 @ X53 @ X50)) @ X50)
% 0.21/0.57          | (r2_hidden @ (sk_C_1 @ X53 @ X50) @ X53))),
% 0.21/0.57      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.21/0.57  thf(l1_zfmisc_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (![X33 : $i, X35 : $i]:
% 0.21/0.57         ((r1_tarski @ (k1_tarski @ X33) @ X35) | ~ (r2_hidden @ X33 @ X35))),
% 0.21/0.57      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.21/0.57          | ((X1) = (k2_relat_1 @ X0))
% 0.21/0.57          | (r1_tarski @ 
% 0.21/0.57             (k1_tarski @ (k4_tarski @ (sk_D_1 @ X1 @ X0) @ (sk_C_1 @ X1 @ X0))) @ 
% 0.21/0.57             X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.57  thf(t3_xboole_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.21/0.57          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.57          | ((k1_tarski @ 
% 0.21/0.57              (k4_tarski @ (sk_D_1 @ X0 @ k1_xboole_0) @ 
% 0.21/0.57               (sk_C_1 @ X0 @ k1_xboole_0)))
% 0.21/0.57              = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.57  thf(t20_zfmisc_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.57         ( k1_tarski @ A ) ) <=>
% 0.21/0.57       ( ( A ) != ( B ) ) ))).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (![X38 : $i, X39 : $i]:
% 0.21/0.57         (((X39) != (X38))
% 0.21/0.57          | ((k4_xboole_0 @ (k1_tarski @ X39) @ (k1_tarski @ X38))
% 0.21/0.57              != (k1_tarski @ X39)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      (![X38 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ (k1_tarski @ X38) @ (k1_tarski @ X38))
% 0.21/0.57           != (k1_tarski @ X38))),
% 0.21/0.57      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.57  thf(t69_enumset1, axiom,
% 0.21/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.57  thf('7', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.57  thf(t19_zfmisc_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.21/0.57       ( k1_tarski @ A ) ))).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      (![X36 : $i, X37 : $i]:
% 0.21/0.57         ((k3_xboole_0 @ (k1_tarski @ X36) @ (k2_tarski @ X36 @ X37))
% 0.21/0.57           = (k1_tarski @ X36))),
% 0.21/0.57      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.21/0.57           = (k1_tarski @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.57  thf('10', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.57  thf(t12_setfam_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      (![X41 : $i, X42 : $i]:
% 0.21/0.57         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.21/0.57      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k1_setfam_1 @ (k1_tarski @ (k1_tarski @ X0))) = (k1_tarski @ X0))),
% 0.21/0.57      inference('demod', [status(thm)], ['9', '12'])).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.57  thf(t100_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (![X1 : $i, X2 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X1 @ X2)
% 0.21/0.57           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X0 @ X0)
% 0.21/0.57           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.21/0.57           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['13', '16'])).
% 0.21/0.57  thf(t92_xboole_1, axiom,
% 0.21/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.57  thf('18', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.21/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.57  thf('20', plain, (![X38 : $i]: ((k1_xboole_0) != (k1_tarski @ X38))),
% 0.21/0.57      inference('demod', [status(thm)], ['6', '19'])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.57          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.21/0.57      inference('clc', [status(thm)], ['4', '20'])).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (![X33 : $i, X35 : $i]:
% 0.21/0.57         ((r1_tarski @ (k1_tarski @ X33) @ X35) | ~ (r2_hidden @ X33 @ X35))),
% 0.21/0.57      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.21/0.57          | (r1_tarski @ (k1_tarski @ (sk_C_1 @ X0 @ k1_xboole_0)) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      ((((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.21/0.57        | ((k1_tarski @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.57  thf('26', plain, (![X38 : $i]: ((k1_xboole_0) != (k1_tarski @ X38))),
% 0.21/0.57      inference('demod', [status(thm)], ['6', '19'])).
% 0.21/0.57  thf('27', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.21/0.57      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.57  thf(t7_xboole_0, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.57          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.57  thf(t18_relat_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( v1_relat_1 @ B ) =>
% 0.21/0.57       ( ~( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) & 
% 0.21/0.57            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      (![X55 : $i, X56 : $i]:
% 0.21/0.57         ((r2_hidden @ (sk_C_2 @ X55) @ (k2_relat_1 @ X55))
% 0.21/0.57          | ~ (r2_hidden @ X56 @ (k1_relat_1 @ X55))
% 0.21/0.57          | ~ (v1_relat_1 @ X55))),
% 0.21/0.57      inference('cnf', [status(esa)], [t18_relat_1])).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.57          | ~ (v1_relat_1 @ X0)
% 0.21/0.57          | (r2_hidden @ (sk_C_2 @ X0) @ (k2_relat_1 @ X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      (![X33 : $i, X35 : $i]:
% 0.21/0.57         ((r1_tarski @ (k1_tarski @ X33) @ X35) | ~ (r2_hidden @ X33 @ X35))),
% 0.21/0.57      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X0)
% 0.21/0.57          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.57          | (r1_tarski @ (k1_tarski @ (sk_C_2 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      (((r1_tarski @ (k1_tarski @ (sk_C_2 @ k1_xboole_0)) @ k1_xboole_0)
% 0.21/0.57        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.57        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['27', '32'])).
% 0.21/0.57  thf(d1_relat_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( v1_relat_1 @ A ) <=>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.57              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      (![X45 : $i]: ((v1_relat_1 @ X45) | (r2_hidden @ (sk_B_1 @ X45) @ X45))),
% 0.21/0.57      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      (![X33 : $i, X35 : $i]:
% 0.21/0.57         ((r1_tarski @ (k1_tarski @ X33) @ X35) | ~ (r2_hidden @ X33 @ X35))),
% 0.21/0.57      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v1_relat_1 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B_1 @ X0)) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      (((v1_relat_1 @ k1_xboole_0)
% 0.21/0.57        | ((k1_tarski @ (sk_B_1 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.57  thf('39', plain, (![X38 : $i]: ((k1_xboole_0) != (k1_tarski @ X38))),
% 0.21/0.57      inference('demod', [status(thm)], ['6', '19'])).
% 0.21/0.57  thf('40', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.57      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.57  thf('41', plain,
% 0.21/0.57      (((r1_tarski @ (k1_tarski @ (sk_C_2 @ k1_xboole_0)) @ k1_xboole_0)
% 0.21/0.57        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['33', '40'])).
% 0.21/0.57  thf(t60_relat_1, conjecture,
% 0.21/0.57    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.57     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.57        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.21/0.57        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.57         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.57      inference('split', [status(esa)], ['42'])).
% 0.21/0.57  thf('44', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.21/0.57      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.57  thf('45', plain,
% 0.21/0.57      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.57         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.57      inference('split', [status(esa)], ['42'])).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.57         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.57  thf('47', plain, ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.57  thf('48', plain,
% 0.21/0.57      (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.21/0.57       ~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.57      inference('split', [status(esa)], ['42'])).
% 0.21/0.57  thf('49', plain, (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['47', '48'])).
% 0.21/0.57  thf('50', plain, (((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['43', '49'])).
% 0.21/0.57  thf('51', plain,
% 0.21/0.57      ((r1_tarski @ (k1_tarski @ (sk_C_2 @ k1_xboole_0)) @ k1_xboole_0)),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['41', '50'])).
% 0.21/0.57  thf('52', plain,
% 0.21/0.57      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.57  thf('53', plain, (((k1_tarski @ (sk_C_2 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.57  thf('54', plain, (![X38 : $i]: ((k1_xboole_0) != (k1_tarski @ X38))),
% 0.21/0.57      inference('demod', [status(thm)], ['6', '19'])).
% 0.21/0.57  thf('55', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.57  thf('56', plain, ($false), inference('simplify', [status(thm)], ['55'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

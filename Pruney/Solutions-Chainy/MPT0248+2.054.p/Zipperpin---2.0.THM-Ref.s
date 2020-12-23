%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CxyzXiYswG

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:25 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 243 expanded)
%              Number of leaves         :   23 (  75 expanded)
%              Depth                    :   19
%              Number of atoms          :  607 (2544 expanded)
%              Number of equality atoms :   96 ( 497 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ( X17 != X18 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ X18 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ( r1_tarski @ X20 @ ( k2_xboole_0 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_C_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['5','6'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('8',plain,(
    ! [X57: $i,X58: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X57 ) @ X58 )
      | ( r2_hidden @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('14',plain,
    ( ( k1_xboole_0 = sk_C_2 )
    | ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('15',plain,(
    ! [X59: $i,X60: $i] :
      ( ( ( k3_xboole_0 @ X60 @ ( k1_tarski @ X59 ) )
        = ( k1_tarski @ X59 ) )
      | ~ ( r2_hidden @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('16',plain,
    ( ( k1_xboole_0 = sk_C_2 )
    | ( ( k3_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('21',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('23',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_xboole_0 = sk_B_1 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X59: $i,X60: $i] :
      ( ( ( k3_xboole_0 @ X60 @ ( k1_tarski @ X59 ) )
        = ( k1_tarski @ X59 ) )
      | ~ ( r2_hidden @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('28',plain,
    ( ( k1_xboole_0 = sk_B_1 )
    | ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('30',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
    | ( k1_xboole_0 = sk_B_1 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('32',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( k1_xboole_0 = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_xboole_0 = sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('36',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k3_xboole_0 @ X9 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('42',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k3_xboole_0 @ X13 @ X16 ) )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['34','44'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('46',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_xboole_0 @ X24 @ X23 )
        = X23 )
      | ~ ( r1_tarski @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['33','47'])).

thf('49',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['19','48'])).

thf('50',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('53',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,
    ( ( k1_xboole_0 = sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('56',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('57',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['52','54','58'])).

thf('60',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['51','59'])).

thf('61',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['49','60'])).

thf('62',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('63',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['61','62'])).

thf('64',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['18','63'])).

thf('65',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['16','64'])).

thf('66',plain,
    ( sk_C_2
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['7','65'])).

thf('67',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['51','59'])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CxyzXiYswG
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 447 iterations in 0.209s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.46/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(t43_zfmisc_1, conjecture,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.46/0.66          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.46/0.66          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.46/0.66          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.66        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.46/0.66             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.46/0.66             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.46/0.66             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.46/0.66  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(d10_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (![X17 : $i, X18 : $i]: ((r1_tarski @ X17 @ X18) | ((X17) != (X18)))),
% 0.46/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.66  thf('2', plain, (![X18 : $i]: (r1_tarski @ X18 @ X18)),
% 0.46/0.66      inference('simplify', [status(thm)], ['1'])).
% 0.46/0.66  thf(t10_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.66         (~ (r1_tarski @ X20 @ X21)
% 0.46/0.66          | (r1_tarski @ X20 @ (k2_xboole_0 @ X22 @ X21)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.66  thf('5', plain, ((r1_tarski @ sk_C_2 @ (k1_tarski @ sk_A))),
% 0.46/0.66      inference('sup+', [status(thm)], ['0', '4'])).
% 0.46/0.66  thf(t28_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (![X25 : $i, X26 : $i]:
% 0.46/0.66         (((k3_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_tarski @ X25 @ X26))),
% 0.46/0.66      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.66  thf('7', plain, (((k3_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A)) = (sk_C_2))),
% 0.46/0.66      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.66  thf(l27_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      (![X57 : $i, X58 : $i]:
% 0.46/0.66         ((r1_xboole_0 @ (k1_tarski @ X57) @ X58) | (r2_hidden @ X57 @ X58))),
% 0.46/0.66      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.46/0.66  thf(d7_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.46/0.66       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X9 : $i, X10 : $i]:
% 0.46/0.66         (((k3_xboole_0 @ X9 @ X10) = (k1_xboole_0))
% 0.46/0.66          | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.46/0.66      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((r2_hidden @ X1 @ X0)
% 0.46/0.66          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.66  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ X0 @ X1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['10', '11'])).
% 0.46/0.66  thf('13', plain, (((k3_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A)) = (sk_C_2))),
% 0.46/0.66      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      ((((k1_xboole_0) = (sk_C_2)) | (r2_hidden @ sk_A @ sk_C_2))),
% 0.46/0.66      inference('sup+', [status(thm)], ['12', '13'])).
% 0.46/0.66  thf(l31_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( r2_hidden @ A @ B ) =>
% 0.46/0.66       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (![X59 : $i, X60 : $i]:
% 0.46/0.66         (((k3_xboole_0 @ X60 @ (k1_tarski @ X59)) = (k1_tarski @ X59))
% 0.46/0.66          | ~ (r2_hidden @ X59 @ X60))),
% 0.46/0.66      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      ((((k1_xboole_0) = (sk_C_2))
% 0.46/0.66        | ((k3_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.46/0.66      inference('split', [status(esa)], ['17'])).
% 0.46/0.66  thf('19', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ X0 @ X1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['10', '11'])).
% 0.46/0.66  thf('21', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(t7_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.66  thf('22', plain,
% 0.46/0.66      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.66  thf('23', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.46/0.66      inference('sup+', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      (![X25 : $i, X26 : $i]:
% 0.46/0.66         (((k3_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_tarski @ X25 @ X26))),
% 0.46/0.66      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.66  thf('25', plain, (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.66  thf('26', plain,
% 0.46/0.66      ((((k1_xboole_0) = (sk_B_1)) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['20', '25'])).
% 0.46/0.66  thf('27', plain,
% 0.46/0.66      (![X59 : $i, X60 : $i]:
% 0.46/0.66         (((k3_xboole_0 @ X60 @ (k1_tarski @ X59)) = (k1_tarski @ X59))
% 0.46/0.66          | ~ (r2_hidden @ X59 @ X60))),
% 0.46/0.66      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      ((((k1_xboole_0) = (sk_B_1))
% 0.46/0.66        | ((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.66  thf('29', plain, (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.66  thf('30', plain,
% 0.46/0.66      ((((k1_tarski @ sk_A) = (sk_B_1)) | ((k1_xboole_0) = (sk_B_1)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('31', plain,
% 0.46/0.66      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.46/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('split', [status(esa)], ['17'])).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      (((((sk_B_1) != (sk_B_1)) | ((k1_xboole_0) = (sk_B_1))))
% 0.46/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      ((((k1_xboole_0) = (sk_B_1))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['32'])).
% 0.46/0.66  thf(d3_tarski, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      (![X6 : $i, X8 : $i]:
% 0.46/0.66         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.66  thf('36', plain,
% 0.46/0.66      (![X25 : $i, X26 : $i]:
% 0.46/0.66         (((k3_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_tarski @ X25 @ X26))),
% 0.46/0.66      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      (![X9 : $i, X11 : $i]:
% 0.46/0.66         ((r1_xboole_0 @ X9 @ X11)
% 0.46/0.66          | ((k3_xboole_0 @ X9 @ X11) != (k1_xboole_0)))),
% 0.46/0.66      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((X0) != (k1_xboole_0))
% 0.46/0.66          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      (![X1 : $i]:
% 0.46/0.66         (r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))),
% 0.46/0.66      inference('simplify', [status(thm)], ['39'])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.66  thf(t4_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.66            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.66       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.66            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X15 @ (k3_xboole_0 @ X13 @ X16))
% 0.46/0.66          | ~ (r1_xboole_0 @ X13 @ X16))),
% 0.46/0.66      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X2 @ X0)
% 0.46/0.66          | ~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.66  thf('44', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.46/0.66      inference('sup-', [status(thm)], ['40', '43'])).
% 0.46/0.66  thf('45', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.46/0.66      inference('sup-', [status(thm)], ['34', '44'])).
% 0.46/0.66  thf(t12_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      (![X23 : $i, X24 : $i]:
% 0.46/0.66         (((k2_xboole_0 @ X24 @ X23) = (X23)) | ~ (r1_tarski @ X24 @ X23))),
% 0.46/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.66  thf('47', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      ((![X0 : $i]: ((k2_xboole_0 @ sk_B_1 @ X0) = (X0)))
% 0.46/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['33', '47'])).
% 0.46/0.66  thf('49', plain,
% 0.46/0.66      ((((k1_tarski @ sk_A) = (sk_C_2)))
% 0.46/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['19', '48'])).
% 0.46/0.66  thf('50', plain,
% 0.46/0.66      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.46/0.66         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('split', [status(esa)], ['50'])).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.46/0.66      inference('split', [status(esa)], ['50'])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('54', plain,
% 0.46/0.66      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | 
% 0.46/0.66       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['53'])).
% 0.46/0.66  thf('55', plain,
% 0.46/0.66      ((((k1_xboole_0) = (sk_B_1))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['32'])).
% 0.46/0.66  thf('56', plain,
% 0.46/0.66      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.46/0.66      inference('split', [status(esa)], ['50'])).
% 0.46/0.66  thf('57', plain,
% 0.46/0.66      ((((sk_B_1) != (sk_B_1)))
% 0.46/0.66         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.46/0.66             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.66  thf('58', plain,
% 0.46/0.66      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['57'])).
% 0.46/0.66  thf('59', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.46/0.66      inference('sat_resolution*', [status(thm)], ['52', '54', '58'])).
% 0.46/0.66  thf('60', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['51', '59'])).
% 0.46/0.66  thf('61', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['49', '60'])).
% 0.46/0.66  thf('62', plain,
% 0.46/0.66      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['17'])).
% 0.46/0.66  thf('63', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.46/0.66      inference('sat_resolution*', [status(thm)], ['61', '62'])).
% 0.46/0.66  thf('64', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['18', '63'])).
% 0.46/0.66  thf('65', plain,
% 0.46/0.66      (((k3_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['16', '64'])).
% 0.46/0.66  thf('66', plain, (((sk_C_2) = (k1_tarski @ sk_A))),
% 0.46/0.66      inference('sup+', [status(thm)], ['7', '65'])).
% 0.46/0.66  thf('67', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['51', '59'])).
% 0.46/0.66  thf('68', plain, ($false),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

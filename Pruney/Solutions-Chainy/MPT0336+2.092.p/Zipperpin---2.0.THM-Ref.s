%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BkrV4jdkrJ

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:32 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 120 expanded)
%              Number of leaves         :   23 (  46 expanded)
%              Depth                    :   18
%              Number of atoms          :  521 ( 949 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k4_xboole_0 @ X30 @ ( k1_tarski @ X31 ) )
        = X30 )
      | ( r2_hidden @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X23 @ X24 )
      | ( r1_xboole_0 @ X23 @ ( k4_xboole_0 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X2 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('20',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_C_2 @ sk_B )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_2 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ sk_D @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['17','30'])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('33',plain,(
    r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X23 @ X24 )
      | ( r1_xboole_0 @ X23 @ ( k4_xboole_0 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('43',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('49',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('50',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_xboole_0 @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['3','51'])).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('54',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['0','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BkrV4jdkrJ
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:18:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 1.97/2.18  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.97/2.18  % Solved by: fo/fo7.sh
% 1.97/2.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.97/2.18  % done 3900 iterations in 1.727s
% 1.97/2.18  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.97/2.18  % SZS output start Refutation
% 1.97/2.18  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.97/2.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.97/2.18  thf(sk_D_type, type, sk_D: $i).
% 1.97/2.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.97/2.18  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.97/2.18  thf(sk_B_type, type, sk_B: $i).
% 1.97/2.18  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.97/2.18  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.97/2.18  thf(sk_A_type, type, sk_A: $i).
% 1.97/2.18  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.97/2.18  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.97/2.18  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.97/2.18  thf(t149_zfmisc_1, conjecture,
% 1.97/2.18    (![A:$i,B:$i,C:$i,D:$i]:
% 1.97/2.18     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.97/2.18         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.97/2.18       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.97/2.18  thf(zf_stmt_0, negated_conjecture,
% 1.97/2.18    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.97/2.18        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.97/2.18            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.97/2.18          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.97/2.18    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.97/2.18  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 1.97/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.18  thf('1', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 1.97/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.18  thf(symmetry_r1_xboole_0, axiom,
% 1.97/2.18    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.97/2.18  thf('2', plain,
% 1.97/2.18      (![X2 : $i, X3 : $i]:
% 1.97/2.18         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.97/2.18      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.97/2.18  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 1.97/2.18      inference('sup-', [status(thm)], ['1', '2'])).
% 1.97/2.18  thf(t65_zfmisc_1, axiom,
% 1.97/2.18    (![A:$i,B:$i]:
% 1.97/2.18     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.97/2.18       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.97/2.18  thf('4', plain,
% 1.97/2.18      (![X30 : $i, X31 : $i]:
% 1.97/2.18         (((k4_xboole_0 @ X30 @ (k1_tarski @ X31)) = (X30))
% 1.97/2.18          | (r2_hidden @ X31 @ X30))),
% 1.97/2.18      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 1.97/2.18  thf(t48_xboole_1, axiom,
% 1.97/2.18    (![A:$i,B:$i]:
% 1.97/2.18     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.97/2.18  thf('5', plain,
% 1.97/2.18      (![X14 : $i, X15 : $i]:
% 1.97/2.18         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.97/2.18           = (k3_xboole_0 @ X14 @ X15))),
% 1.97/2.18      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.97/2.18  thf(t36_xboole_1, axiom,
% 1.97/2.18    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.97/2.18  thf('6', plain,
% 1.97/2.18      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.97/2.18      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.97/2.18  thf('7', plain,
% 1.97/2.18      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.97/2.18      inference('sup+', [status(thm)], ['5', '6'])).
% 1.97/2.18  thf(t85_xboole_1, axiom,
% 1.97/2.18    (![A:$i,B:$i,C:$i]:
% 1.97/2.18     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 1.97/2.18  thf('8', plain,
% 1.97/2.18      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.97/2.18         (~ (r1_tarski @ X23 @ X24)
% 1.97/2.18          | (r1_xboole_0 @ X23 @ (k4_xboole_0 @ X25 @ X24)))),
% 1.97/2.18      inference('cnf', [status(esa)], [t85_xboole_1])).
% 1.97/2.18  thf('9', plain,
% 1.97/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.18         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0))),
% 1.97/2.18      inference('sup-', [status(thm)], ['7', '8'])).
% 1.97/2.18  thf('10', plain,
% 1.97/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.18         ((r1_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X2) @ X0)
% 1.97/2.18          | (r2_hidden @ X1 @ X0))),
% 1.97/2.18      inference('sup+', [status(thm)], ['4', '9'])).
% 1.97/2.18  thf(t4_xboole_0, axiom,
% 1.97/2.18    (![A:$i,B:$i]:
% 1.97/2.18     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.97/2.18            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.97/2.18       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.97/2.18            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.97/2.18  thf('11', plain,
% 1.97/2.18      (![X8 : $i, X9 : $i]:
% 1.97/2.18         ((r1_xboole_0 @ X8 @ X9)
% 1.97/2.18          | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 1.97/2.18      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.97/2.18  thf('12', plain,
% 1.97/2.18      (![X8 : $i, X9 : $i]:
% 1.97/2.18         ((r1_xboole_0 @ X8 @ X9)
% 1.97/2.18          | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 1.97/2.18      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.97/2.18  thf(t3_xboole_0, axiom,
% 1.97/2.18    (![A:$i,B:$i]:
% 1.97/2.18     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.97/2.18            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.97/2.18       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.97/2.18            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.97/2.18  thf('13', plain,
% 1.97/2.18      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.97/2.18         (~ (r2_hidden @ X6 @ X4)
% 1.97/2.18          | ~ (r2_hidden @ X6 @ X7)
% 1.97/2.18          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.97/2.18      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.97/2.18  thf('14', plain,
% 1.97/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.18         ((r1_xboole_0 @ X1 @ X0)
% 1.97/2.18          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.97/2.18          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 1.97/2.18      inference('sup-', [status(thm)], ['12', '13'])).
% 1.97/2.18  thf('15', plain,
% 1.97/2.18      (![X0 : $i, X1 : $i]:
% 1.97/2.18         ((r1_xboole_0 @ X1 @ X0)
% 1.97/2.18          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.97/2.18          | (r1_xboole_0 @ X1 @ X0))),
% 1.97/2.18      inference('sup-', [status(thm)], ['11', '14'])).
% 1.97/2.18  thf('16', plain,
% 1.97/2.18      (![X0 : $i, X1 : $i]:
% 1.97/2.18         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.97/2.18          | (r1_xboole_0 @ X1 @ X0))),
% 1.97/2.18      inference('simplify', [status(thm)], ['15'])).
% 1.97/2.18  thf('17', plain,
% 1.97/2.18      (![X0 : $i, X1 : $i]:
% 1.97/2.18         ((r2_hidden @ X1 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0))
% 1.97/2.18          | (r1_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 1.97/2.18      inference('sup-', [status(thm)], ['10', '16'])).
% 1.97/2.18  thf(commutativity_k3_xboole_0, axiom,
% 1.97/2.18    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.97/2.18  thf('18', plain,
% 1.97/2.18      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.97/2.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.97/2.18  thf('19', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 1.97/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.18  thf(t83_xboole_1, axiom,
% 1.97/2.18    (![A:$i,B:$i]:
% 1.97/2.18     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.97/2.18  thf('20', plain,
% 1.97/2.18      (![X20 : $i, X21 : $i]:
% 1.97/2.18         (((k4_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_xboole_0 @ X20 @ X21))),
% 1.97/2.18      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.97/2.18  thf('21', plain, (((k4_xboole_0 @ sk_C_2 @ sk_B) = (sk_C_2))),
% 1.97/2.18      inference('sup-', [status(thm)], ['19', '20'])).
% 1.97/2.18  thf('22', plain,
% 1.97/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.18         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0))),
% 1.97/2.18      inference('sup-', [status(thm)], ['7', '8'])).
% 1.97/2.18  thf('23', plain,
% 1.97/2.18      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_C_2)),
% 1.97/2.18      inference('sup+', [status(thm)], ['21', '22'])).
% 1.97/2.18  thf('24', plain,
% 1.97/2.18      (![X2 : $i, X3 : $i]:
% 1.97/2.18         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.97/2.18      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.97/2.18  thf('25', plain,
% 1.97/2.18      (![X0 : $i]: (r1_xboole_0 @ sk_C_2 @ (k3_xboole_0 @ sk_B @ X0))),
% 1.97/2.18      inference('sup-', [status(thm)], ['23', '24'])).
% 1.97/2.18  thf('26', plain, ((r2_hidden @ sk_D @ sk_C_2)),
% 1.97/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.18  thf('27', plain,
% 1.97/2.18      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.97/2.18         (~ (r2_hidden @ X6 @ X4)
% 1.97/2.18          | ~ (r2_hidden @ X6 @ X7)
% 1.97/2.18          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.97/2.18      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.97/2.18  thf('28', plain,
% 1.97/2.18      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 1.97/2.18      inference('sup-', [status(thm)], ['26', '27'])).
% 1.97/2.18  thf('29', plain,
% 1.97/2.18      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ X0))),
% 1.97/2.18      inference('sup-', [status(thm)], ['25', '28'])).
% 1.97/2.18  thf('30', plain,
% 1.97/2.18      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ X0 @ sk_B))),
% 1.97/2.18      inference('sup-', [status(thm)], ['18', '29'])).
% 1.97/2.18  thf('31', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 1.97/2.18      inference('sup-', [status(thm)], ['17', '30'])).
% 1.97/2.18  thf('32', plain,
% 1.97/2.18      (![X2 : $i, X3 : $i]:
% 1.97/2.18         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.97/2.18      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.97/2.18  thf('33', plain, ((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D))),
% 1.97/2.18      inference('sup-', [status(thm)], ['31', '32'])).
% 1.97/2.18  thf('34', plain,
% 1.97/2.18      (![X20 : $i, X21 : $i]:
% 1.97/2.18         (((k4_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_xboole_0 @ X20 @ X21))),
% 1.97/2.18      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.97/2.18  thf('35', plain, (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (sk_B))),
% 1.97/2.18      inference('sup-', [status(thm)], ['33', '34'])).
% 1.97/2.18  thf('36', plain,
% 1.97/2.18      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 1.97/2.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.18  thf('37', plain,
% 1.97/2.18      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.97/2.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.97/2.18  thf('38', plain,
% 1.97/2.18      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 1.97/2.18      inference('demod', [status(thm)], ['36', '37'])).
% 1.97/2.18  thf('39', plain,
% 1.97/2.18      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.97/2.18         (~ (r1_tarski @ X23 @ X24)
% 1.97/2.18          | (r1_xboole_0 @ X23 @ (k4_xboole_0 @ X25 @ X24)))),
% 1.97/2.18      inference('cnf', [status(esa)], [t85_xboole_1])).
% 1.97/2.18  thf('40', plain,
% 1.97/2.18      (![X0 : $i]:
% 1.97/2.18         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 1.97/2.18          (k4_xboole_0 @ X0 @ (k1_tarski @ sk_D)))),
% 1.97/2.18      inference('sup-', [status(thm)], ['38', '39'])).
% 1.97/2.18  thf('41', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 1.97/2.18      inference('sup+', [status(thm)], ['35', '40'])).
% 1.97/2.18  thf('42', plain,
% 1.97/2.18      (![X20 : $i, X21 : $i]:
% 1.97/2.18         (((k4_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_xboole_0 @ X20 @ X21))),
% 1.97/2.18      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.97/2.18  thf('43', plain,
% 1.97/2.18      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)
% 1.97/2.18         = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.97/2.18      inference('sup-', [status(thm)], ['41', '42'])).
% 1.97/2.18  thf('44', plain,
% 1.97/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.18         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0))),
% 1.97/2.18      inference('sup-', [status(thm)], ['7', '8'])).
% 1.97/2.18  thf('45', plain,
% 1.97/2.18      (![X2 : $i, X3 : $i]:
% 1.97/2.18         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.97/2.18      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.97/2.18  thf('46', plain,
% 1.97/2.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.18         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X2))),
% 1.97/2.18      inference('sup-', [status(thm)], ['44', '45'])).
% 1.97/2.18  thf('47', plain,
% 1.97/2.18      (![X0 : $i]:
% 1.97/2.18         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k3_xboole_0 @ sk_B @ X0))),
% 1.97/2.18      inference('sup+', [status(thm)], ['43', '46'])).
% 1.97/2.18  thf('48', plain,
% 1.97/2.18      (![X0 : $i, X1 : $i]:
% 1.97/2.18         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.97/2.18          | (r1_xboole_0 @ X1 @ X0))),
% 1.97/2.18      inference('simplify', [status(thm)], ['15'])).
% 1.97/2.18  thf('49', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 1.97/2.18      inference('sup-', [status(thm)], ['47', '48'])).
% 1.97/2.18  thf(t70_xboole_1, axiom,
% 1.97/2.18    (![A:$i,B:$i,C:$i]:
% 1.97/2.18     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.97/2.18            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.97/2.18       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.97/2.18            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.97/2.18  thf('50', plain,
% 1.97/2.18      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.97/2.18         ((r1_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 1.97/2.18          | ~ (r1_xboole_0 @ X16 @ X17)
% 1.97/2.18          | ~ (r1_xboole_0 @ X16 @ X18))),
% 1.97/2.18      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.97/2.18  thf('51', plain,
% 1.97/2.18      (![X0 : $i]:
% 1.97/2.18         (~ (r1_xboole_0 @ sk_B @ X0)
% 1.97/2.18          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.97/2.18      inference('sup-', [status(thm)], ['49', '50'])).
% 1.97/2.18  thf('52', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_2))),
% 1.97/2.18      inference('sup-', [status(thm)], ['3', '51'])).
% 1.97/2.18  thf('53', plain,
% 1.97/2.18      (![X2 : $i, X3 : $i]:
% 1.97/2.18         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.97/2.18      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.97/2.18  thf('54', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 1.97/2.18      inference('sup-', [status(thm)], ['52', '53'])).
% 1.97/2.18  thf('55', plain, ($false), inference('demod', [status(thm)], ['0', '54'])).
% 1.97/2.18  
% 1.97/2.18  % SZS output end Refutation
% 1.97/2.18  
% 1.97/2.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

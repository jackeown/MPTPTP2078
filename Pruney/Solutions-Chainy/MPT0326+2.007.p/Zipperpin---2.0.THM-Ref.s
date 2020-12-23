%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mmorCmKSRC

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 135 expanded)
%              Number of leaves         :   25 (  49 expanded)
%              Depth                    :   20
%              Number of atoms          :  531 (1105 expanded)
%              Number of equality atoms :   47 (  74 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t139_zfmisc_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i,C: $i,D: $i] :
          ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
            | ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) )
         => ( r1_tarski @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i,C: $i,D: $i] :
            ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
              | ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) )
           => ( r1_tarski @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t139_zfmisc_1])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C_1 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['1'])).

thf(t138_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_zfmisc_1 @ X23 @ X24 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X23 @ X24 ) @ ( k2_zfmisc_1 @ X25 @ X26 ) )
      | ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('5',plain,
    ( ( ( r1_tarski @ sk_B_1 @ sk_D )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X21 @ X20 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('9',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( sk_A = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( ( k4_xboole_0 @ X10 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['12','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('28',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('30',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('34',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_xboole_0 @ X3 @ X5 )
      | ( ( k3_xboole_0 @ X3 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['32','36'])).

thf('38',plain,(
    ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['27','37'])).

thf('39',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C_1 ) )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['1'])).

thf('40',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['2','40'])).

thf('42',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_zfmisc_1 @ X23 @ X24 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X23 @ X24 ) @ ( k2_zfmisc_1 @ X25 @ X26 ) )
      | ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('43',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k2_zfmisc_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X21 @ X20 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('52',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['32','36'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mmorCmKSRC
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 59 iterations in 0.027s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(t139_zfmisc_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.48       ( ![B:$i,C:$i,D:$i]:
% 0.20/0.48         ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) | 
% 0.20/0.48             ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) ) =>
% 0.20/0.48           ( r1_tarski @ B @ D ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.48          ( ![B:$i,C:$i,D:$i]:
% 0.20/0.48            ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) | 
% 0.20/0.48                ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) ) =>
% 0.20/0.48              ( r1_tarski @ B @ D ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t139_zfmisc_1])).
% 0.20/0.48  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.48         (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 0.20/0.48        | (r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.20/0.48           (k2_zfmisc_1 @ sk_D @ sk_C_1)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.20/0.48         (k2_zfmisc_1 @ sk_D @ sk_C_1)))
% 0.20/0.48         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.20/0.48               (k2_zfmisc_1 @ sk_D @ sk_C_1))))),
% 0.20/0.48      inference('split', [status(esa)], ['1'])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.48         (k2_zfmisc_1 @ sk_C_1 @ sk_D)))
% 0.20/0.48         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.48               (k2_zfmisc_1 @ sk_C_1 @ sk_D))))),
% 0.20/0.48      inference('split', [status(esa)], ['1'])).
% 0.20/0.48  thf(t138_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.20/0.48       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.48         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.48         (((k2_zfmisc_1 @ X23 @ X24) = (k1_xboole_0))
% 0.20/0.48          | ~ (r1_tarski @ (k2_zfmisc_1 @ X23 @ X24) @ 
% 0.20/0.48               (k2_zfmisc_1 @ X25 @ X26))
% 0.20/0.48          | (r1_tarski @ X24 @ X26))),
% 0.20/0.48      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      ((((r1_tarski @ sk_B_1 @ sk_D)
% 0.20/0.48         | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))
% 0.20/0.48         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.48               (k2_zfmisc_1 @ sk_C_1 @ sk_D))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf('6', plain, (~ (r1_tarski @ sk_B_1 @ sk_D)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.20/0.48         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.48               (k2_zfmisc_1 @ sk_C_1 @ sk_D))))),
% 0.20/0.48      inference('clc', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf(t113_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X20 : $i, X21 : $i]:
% 0.20/0.48         (((X20) = (k1_xboole_0))
% 0.20/0.48          | ((X21) = (k1_xboole_0))
% 0.20/0.48          | ((k2_zfmisc_1 @ X21 @ X20) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48         | ((sk_A) = (k1_xboole_0))
% 0.20/0.48         | ((sk_B_1) = (k1_xboole_0))))
% 0.20/0.48         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.48               (k2_zfmisc_1 @ sk_C_1 @ sk_D))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.48         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.48               (k2_zfmisc_1 @ sk_C_1 @ sk_D))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.48  thf('11', plain, (~ (r1_tarski @ sk_B_1 @ sk_D)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.48         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.48               (k2_zfmisc_1 @ sk_C_1 @ sk_D))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf(t2_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X18 : $i]: ((k3_xboole_0 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.48  thf(t100_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ X13 @ X14)
% 0.20/0.48           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf(t5_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.48  thf('16', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.48  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf(l32_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         ((r1_tarski @ X10 @ X11)
% 0.20/0.48          | ((k4_xboole_0 @ X10 @ X11) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X18 : $i]: ((k3_xboole_0 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.48  thf(t18_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.48         ((r1_tarski @ X15 @ X16)
% 0.20/0.48          | ~ (r1_tarski @ X15 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r1_tarski @ X1 @ k1_xboole_0) | (r1_tarski @ X1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('24', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.48      inference('sup-', [status(thm)], ['20', '23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      ((((sk_A) = (k1_xboole_0)))
% 0.20/0.48         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.48               (k2_zfmisc_1 @ sk_C_1 @ sk_D))))),
% 0.20/0.48      inference('demod', [status(thm)], ['12', '24'])).
% 0.20/0.48  thf('26', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.20/0.48         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.48               (k2_zfmisc_1 @ sk_C_1 @ sk_D))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf(d1_xboole_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X18 : $i]: ((k3_xboole_0 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.48  thf(t4_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.48            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.20/0.48          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '31'])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X18 : $i]: ((k3_xboole_0 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.48  thf(d7_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.48       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (![X3 : $i, X5 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ X3 @ X5) | ((k3_xboole_0 @ X3 @ X5) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.48  thf('36', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.20/0.48      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.48  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('demod', [status(thm)], ['32', '36'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (~
% 0.20/0.48       ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.48         (k2_zfmisc_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.48      inference('demod', [status(thm)], ['27', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.20/0.48         (k2_zfmisc_1 @ sk_D @ sk_C_1))) | 
% 0.20/0.48       ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.48         (k2_zfmisc_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.48      inference('split', [status(esa)], ['1'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.20/0.48         (k2_zfmisc_1 @ sk_D @ sk_C_1)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['38', '39'])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      ((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.20/0.48        (k2_zfmisc_1 @ sk_D @ sk_C_1))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['2', '40'])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.48         (((k2_zfmisc_1 @ X23 @ X24) = (k1_xboole_0))
% 0.20/0.48          | ~ (r1_tarski @ (k2_zfmisc_1 @ X23 @ X24) @ 
% 0.20/0.48               (k2_zfmisc_1 @ X25 @ X26))
% 0.20/0.48          | (r1_tarski @ X23 @ X25))),
% 0.20/0.48      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (((r1_tarski @ sk_B_1 @ sk_D)
% 0.20/0.48        | ((k2_zfmisc_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.48  thf('44', plain, (~ (r1_tarski @ sk_B_1 @ sk_D)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('45', plain, (((k2_zfmisc_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('clc', [status(thm)], ['43', '44'])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (![X20 : $i, X21 : $i]:
% 0.20/0.48         (((X20) = (k1_xboole_0))
% 0.20/0.48          | ((X21) = (k1_xboole_0))
% 0.20/0.48          | ((k2_zfmisc_1 @ X21 @ X20) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.48  thf('48', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.48  thf('49', plain, (~ (r1_tarski @ sk_B_1 @ sk_D)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      ((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.48  thf('51', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.48      inference('sup-', [status(thm)], ['20', '23'])).
% 0.20/0.48  thf('52', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.48  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('demod', [status(thm)], ['32', '36'])).
% 0.20/0.48  thf('54', plain, ($false),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '52', '53'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

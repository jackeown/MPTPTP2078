%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7uaXD2JcXJ

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:39 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 286 expanded)
%              Number of leaves         :   26 (  97 expanded)
%              Depth                    :   24
%              Number of atoms          :  576 (2178 expanded)
%              Number of equality atoms :   66 ( 308 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('2',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X42 ) @ X43 )
      | ( r2_hidden @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('3',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('13',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['11','15'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('17',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k3_xboole_0 @ X45 @ ( k1_tarski @ X44 ) )
        = ( k1_tarski @ X44 ) )
      | ~ ( r2_hidden @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['3','4'])).

thf('20',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','20'])).

thf('22',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['18','19'])).

thf('23',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X42 ) @ X43 )
      | ( r2_hidden @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k3_xboole_0 @ X45 @ ( k1_tarski @ X44 ) )
        = ( k1_tarski @ X44 ) )
      | ~ ( r2_hidden @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['18','19'])).

thf('32',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['18','19'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ( ( k3_xboole_0 @ X0 @ sk_B_1 )
        = sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B_1 @ X0 )
        = sk_B_1 )
      | ( r1_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('38',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ X0 @ sk_B_1 ) ) )
      | ( r1_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('41',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('42',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('45',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = X0 )
      | ( r1_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['39','48'])).

thf('50',plain,
    ( ( sk_B_1 = sk_C_1 )
    | ( r1_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['21','49'])).

thf('51',plain,(
    sk_B_1 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('58',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('60',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_C_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','20'])).

thf('62',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('63',plain,
    ( sk_B_1
    = ( k5_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('65',plain,
    ( sk_C_1
    = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('67',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7uaXD2JcXJ
% 0.16/0.37  % Computer   : n008.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 09:39:45 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.61/0.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.85  % Solved by: fo/fo7.sh
% 0.61/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.85  % done 938 iterations in 0.360s
% 0.61/0.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.85  % SZS output start Refutation
% 0.61/0.85  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.61/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.85  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.85  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.61/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.85  thf(sk_B_type, type, sk_B: $i > $i).
% 0.61/0.85  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.61/0.85  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.61/0.85  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.61/0.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.85  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.61/0.85  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.61/0.85  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.61/0.85  thf(t44_zfmisc_1, conjecture,
% 0.61/0.85    (![A:$i,B:$i,C:$i]:
% 0.61/0.85     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.61/0.85          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.61/0.85          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.61/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.85    (~( ![A:$i,B:$i,C:$i]:
% 0.61/0.85        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.61/0.85             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.61/0.85             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.61/0.85    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.61/0.85  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf(d1_xboole_0, axiom,
% 0.61/0.85    (![A:$i]:
% 0.61/0.85     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.61/0.85  thf('1', plain,
% 0.61/0.85      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.61/0.85      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.61/0.85  thf(l27_zfmisc_1, axiom,
% 0.61/0.85    (![A:$i,B:$i]:
% 0.61/0.85     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.61/0.85  thf('2', plain,
% 0.61/0.85      (![X42 : $i, X43 : $i]:
% 0.61/0.85         ((r1_xboole_0 @ (k1_tarski @ X42) @ X43) | (r2_hidden @ X42 @ X43))),
% 0.61/0.85      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.61/0.85  thf('3', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf(t21_xboole_1, axiom,
% 0.61/0.85    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.61/0.85  thf('4', plain,
% 0.61/0.85      (![X12 : $i, X13 : $i]:
% 0.61/0.85         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 0.61/0.85      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.61/0.85  thf('5', plain, (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1))),
% 0.61/0.85      inference('sup+', [status(thm)], ['3', '4'])).
% 0.61/0.85  thf(commutativity_k3_xboole_0, axiom,
% 0.61/0.85    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.61/0.85  thf('6', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.85  thf(t4_xboole_0, axiom,
% 0.61/0.85    (![A:$i,B:$i]:
% 0.61/0.85     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.61/0.85            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.61/0.85       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.61/0.85            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.61/0.85  thf('7', plain,
% 0.61/0.85      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.61/0.85         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.61/0.85          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.61/0.85      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.61/0.85  thf('8', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.85         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.61/0.85          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.61/0.85      inference('sup-', [status(thm)], ['6', '7'])).
% 0.61/0.85  thf('9', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.61/0.85          | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.61/0.85      inference('sup-', [status(thm)], ['5', '8'])).
% 0.61/0.85  thf('10', plain,
% 0.61/0.85      (![X0 : $i]: ((r2_hidden @ sk_A @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.61/0.85      inference('sup-', [status(thm)], ['2', '9'])).
% 0.61/0.85  thf('11', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.61/0.85      inference('sup-', [status(thm)], ['1', '10'])).
% 0.61/0.85  thf(l13_xboole_0, axiom,
% 0.61/0.85    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.61/0.85  thf('12', plain,
% 0.61/0.85      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.61/0.85      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.61/0.85  thf('13', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('14', plain, (![X0 : $i]: (((sk_B_1) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.61/0.85      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.85  thf('15', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.61/0.85      inference('simplify', [status(thm)], ['14'])).
% 0.61/0.85  thf('16', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.61/0.85      inference('clc', [status(thm)], ['11', '15'])).
% 0.61/0.85  thf(l31_zfmisc_1, axiom,
% 0.61/0.85    (![A:$i,B:$i]:
% 0.61/0.85     ( ( r2_hidden @ A @ B ) =>
% 0.61/0.85       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.61/0.85  thf('17', plain,
% 0.61/0.85      (![X44 : $i, X45 : $i]:
% 0.61/0.85         (((k3_xboole_0 @ X45 @ (k1_tarski @ X44)) = (k1_tarski @ X44))
% 0.61/0.85          | ~ (r2_hidden @ X44 @ X45))),
% 0.61/0.85      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.61/0.85  thf('18', plain,
% 0.61/0.85      (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.61/0.85      inference('sup-', [status(thm)], ['16', '17'])).
% 0.61/0.85  thf('19', plain, (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1))),
% 0.61/0.85      inference('sup+', [status(thm)], ['3', '4'])).
% 0.61/0.85  thf('20', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.61/0.85      inference('sup+', [status(thm)], ['18', '19'])).
% 0.61/0.85  thf('21', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.61/0.85      inference('demod', [status(thm)], ['0', '20'])).
% 0.61/0.85  thf('22', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.61/0.85      inference('sup+', [status(thm)], ['18', '19'])).
% 0.61/0.85  thf('23', plain,
% 0.61/0.85      (![X42 : $i, X43 : $i]:
% 0.61/0.85         ((r1_xboole_0 @ (k1_tarski @ X42) @ X43) | (r2_hidden @ X42 @ X43))),
% 0.61/0.85      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.61/0.85  thf('24', plain,
% 0.61/0.85      (![X8 : $i, X9 : $i]:
% 0.61/0.85         ((r1_xboole_0 @ X8 @ X9)
% 0.61/0.85          | (r2_hidden @ (sk_C @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 0.61/0.85      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.61/0.85  thf('25', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.85         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.61/0.85          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.61/0.85      inference('sup-', [status(thm)], ['6', '7'])).
% 0.61/0.85  thf('26', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i]:
% 0.61/0.85         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.61/0.85      inference('sup-', [status(thm)], ['24', '25'])).
% 0.61/0.85  thf('27', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i]:
% 0.61/0.85         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.61/0.85      inference('sup-', [status(thm)], ['23', '26'])).
% 0.61/0.85  thf('28', plain,
% 0.61/0.85      (![X0 : $i]: ((r1_xboole_0 @ X0 @ sk_B_1) | (r2_hidden @ sk_A @ X0))),
% 0.61/0.85      inference('sup+', [status(thm)], ['22', '27'])).
% 0.61/0.85  thf('29', plain,
% 0.61/0.85      (![X44 : $i, X45 : $i]:
% 0.61/0.85         (((k3_xboole_0 @ X45 @ (k1_tarski @ X44)) = (k1_tarski @ X44))
% 0.61/0.85          | ~ (r2_hidden @ X44 @ X45))),
% 0.61/0.85      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.61/0.85  thf('30', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         ((r1_xboole_0 @ X0 @ sk_B_1)
% 0.61/0.85          | ((k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))),
% 0.61/0.85      inference('sup-', [status(thm)], ['28', '29'])).
% 0.61/0.85  thf('31', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.61/0.85      inference('sup+', [status(thm)], ['18', '19'])).
% 0.61/0.85  thf('32', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.61/0.85      inference('sup+', [status(thm)], ['18', '19'])).
% 0.61/0.85  thf('33', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         ((r1_xboole_0 @ X0 @ sk_B_1)
% 0.61/0.85          | ((k3_xboole_0 @ X0 @ sk_B_1) = (sk_B_1)))),
% 0.61/0.85      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.61/0.85  thf('34', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.85  thf('35', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         (((k3_xboole_0 @ sk_B_1 @ X0) = (sk_B_1))
% 0.61/0.85          | (r1_xboole_0 @ X0 @ sk_B_1))),
% 0.61/0.85      inference('sup+', [status(thm)], ['33', '34'])).
% 0.61/0.85  thf(t94_xboole_1, axiom,
% 0.61/0.85    (![A:$i,B:$i]:
% 0.61/0.85     ( ( k2_xboole_0 @ A @ B ) =
% 0.61/0.85       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.61/0.85  thf('36', plain,
% 0.61/0.85      (![X19 : $i, X20 : $i]:
% 0.61/0.85         ((k2_xboole_0 @ X19 @ X20)
% 0.61/0.85           = (k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ 
% 0.61/0.85              (k3_xboole_0 @ X19 @ X20)))),
% 0.61/0.85      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.61/0.85  thf(t91_xboole_1, axiom,
% 0.61/0.85    (![A:$i,B:$i,C:$i]:
% 0.61/0.85     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.61/0.85       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.61/0.85  thf('37', plain,
% 0.61/0.85      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.61/0.85         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.61/0.85           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.61/0.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.61/0.85  thf('38', plain,
% 0.61/0.85      (![X19 : $i, X20 : $i]:
% 0.61/0.85         ((k2_xboole_0 @ X19 @ X20)
% 0.61/0.85           = (k5_xboole_0 @ X19 @ 
% 0.61/0.85              (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X19 @ X20))))),
% 0.61/0.85      inference('demod', [status(thm)], ['36', '37'])).
% 0.61/0.85  thf('39', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         (((k2_xboole_0 @ sk_B_1 @ X0)
% 0.61/0.85            = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ X0 @ sk_B_1)))
% 0.61/0.85          | (r1_xboole_0 @ X0 @ sk_B_1))),
% 0.61/0.85      inference('sup+', [status(thm)], ['35', '38'])).
% 0.61/0.85  thf(commutativity_k5_xboole_0, axiom,
% 0.61/0.85    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.61/0.85  thf('40', plain,
% 0.61/0.85      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.61/0.85      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.61/0.85  thf(t92_xboole_1, axiom,
% 0.61/0.85    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.61/0.85  thf('41', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.61/0.85      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.61/0.85  thf('42', plain,
% 0.61/0.85      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.61/0.85         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.61/0.85           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.61/0.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.61/0.85  thf('43', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i]:
% 0.61/0.85         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.61/0.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.85      inference('sup+', [status(thm)], ['41', '42'])).
% 0.61/0.85  thf('44', plain,
% 0.61/0.85      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.61/0.85      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.61/0.85  thf(t5_boole, axiom,
% 0.61/0.85    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.61/0.85  thf('45', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.61/0.85      inference('cnf', [status(esa)], [t5_boole])).
% 0.61/0.85  thf('46', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.61/0.85      inference('sup+', [status(thm)], ['44', '45'])).
% 0.61/0.85  thf('47', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i]:
% 0.61/0.85         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.85      inference('demod', [status(thm)], ['43', '46'])).
% 0.61/0.85  thf('48', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i]:
% 0.61/0.85         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.85      inference('sup+', [status(thm)], ['40', '47'])).
% 0.61/0.85  thf('49', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         (((k2_xboole_0 @ sk_B_1 @ X0) = (X0)) | (r1_xboole_0 @ X0 @ sk_B_1))),
% 0.61/0.85      inference('demod', [status(thm)], ['39', '48'])).
% 0.61/0.85  thf('50', plain, ((((sk_B_1) = (sk_C_1)) | (r1_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.61/0.85      inference('sup+', [status(thm)], ['21', '49'])).
% 0.61/0.85  thf('51', plain, (((sk_B_1) != (sk_C_1))),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('52', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B_1)),
% 0.61/0.85      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 0.61/0.85  thf('53', plain,
% 0.61/0.85      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.61/0.85      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.61/0.85  thf('54', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.85         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.61/0.85          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.61/0.85      inference('sup-', [status(thm)], ['6', '7'])).
% 0.61/0.85  thf('55', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i]:
% 0.61/0.85         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.61/0.85      inference('sup-', [status(thm)], ['53', '54'])).
% 0.61/0.85  thf('56', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.61/0.85      inference('sup-', [status(thm)], ['52', '55'])).
% 0.61/0.85  thf('57', plain,
% 0.61/0.85      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.61/0.85      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.61/0.85  thf('58', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (k1_xboole_0))),
% 0.61/0.85      inference('sup-', [status(thm)], ['56', '57'])).
% 0.61/0.85  thf('59', plain,
% 0.61/0.85      (![X19 : $i, X20 : $i]:
% 0.61/0.85         ((k2_xboole_0 @ X19 @ X20)
% 0.61/0.85           = (k5_xboole_0 @ X19 @ 
% 0.61/0.85              (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X19 @ X20))))),
% 0.61/0.85      inference('demod', [status(thm)], ['36', '37'])).
% 0.61/0.85  thf('60', plain,
% 0.61/0.85      (((k2_xboole_0 @ sk_B_1 @ sk_C_1)
% 0.61/0.85         = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_C_1 @ k1_xboole_0)))),
% 0.61/0.85      inference('sup+', [status(thm)], ['58', '59'])).
% 0.61/0.85  thf('61', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.61/0.85      inference('demod', [status(thm)], ['0', '20'])).
% 0.61/0.85  thf('62', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.61/0.85      inference('cnf', [status(esa)], [t5_boole])).
% 0.61/0.85  thf('63', plain, (((sk_B_1) = (k5_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.61/0.85      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.61/0.85  thf('64', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i]:
% 0.61/0.85         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.85      inference('demod', [status(thm)], ['43', '46'])).
% 0.61/0.85  thf('65', plain, (((sk_C_1) = (k5_xboole_0 @ sk_B_1 @ sk_B_1))),
% 0.61/0.85      inference('sup+', [status(thm)], ['63', '64'])).
% 0.61/0.85  thf('66', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.61/0.85      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.61/0.85  thf('67', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.61/0.85      inference('demod', [status(thm)], ['65', '66'])).
% 0.61/0.85  thf('68', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('69', plain, ($false),
% 0.61/0.85      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 0.61/0.85  
% 0.61/0.85  % SZS output end Refutation
% 0.61/0.85  
% 0.61/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

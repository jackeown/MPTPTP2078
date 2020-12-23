%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wxHPwIvWN4

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:35 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 797 expanded)
%              Number of leaves         :   28 ( 257 expanded)
%              Depth                    :   30
%              Number of atoms          : 1228 (8200 expanded)
%              Number of equality atoms :  166 (1141 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X20: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X22 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k4_xboole_0 @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('5',plain,(
    ! [X28: $i] :
      ( ( k4_xboole_0 @ X28 @ k1_xboole_0 )
      = X28 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

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

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X19: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k3_xboole_0 @ X15 @ X18 ) )
      | ~ ( r1_xboole_0 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf(t134_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ C @ D ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( ( A = C )
            & ( B = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t134_zfmisc_1])).

thf('21',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('22',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X55 @ X57 ) @ X56 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X55 @ X56 ) @ ( k2_zfmisc_1 @ X57 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k4_xboole_0 @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('27',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k4_xboole_0 @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('29',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X51 @ X53 ) @ ( k3_xboole_0 @ X52 @ X54 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X51 @ X52 ) @ ( k2_zfmisc_1 @ X53 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_2 @ X0 ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_2 ) ) @ sk_B_1 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['20','30'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k2_zfmisc_1 @ X46 @ X47 )
        = k1_xboole_0 )
      | ( X46 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('33',plain,(
    ! [X47: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X47 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_2 ) ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','33'])).

thf('35',plain,
    ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['7','34'])).

thf('36',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X45 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X46 @ X45 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k4_xboole_0 @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X28: $i] :
      ( ( k4_xboole_0 @ X28 @ k1_xboole_0 )
      = X28 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_2 @ X0 ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('47',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_A ) @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X28: $i] :
      ( ( k4_xboole_0 @ X28 @ k1_xboole_0 )
      = X28 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('49',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X20: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X22 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k4_xboole_0 @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X28: $i] :
      ( ( k4_xboole_0 @ X28 @ k1_xboole_0 )
      = X28 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('56',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['47','56'])).

thf('58',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 )
    = ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('61',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ( r1_tarski @ X49 @ X50 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X48 @ X49 ) @ ( k2_zfmisc_1 @ X48 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
    | ( r1_tarski @ sk_B_1 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('67',plain,(
    r1_tarski @ sk_B_1 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X20: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X22 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('69',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('71',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k4_xboole_0 @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('72',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k4_xboole_0 @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['70','75'])).

thf('77',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','76'])).

thf('78',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k4_xboole_0 @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('79',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X28: $i] :
      ( ( k4_xboole_0 @ X28 @ k1_xboole_0 )
      = X28 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('82',plain,
    ( sk_B_1
    = ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ! [X55: $i,X57: $i,X58: $i] :
      ( ( k2_zfmisc_1 @ X58 @ ( k4_xboole_0 @ X55 @ X57 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X58 @ X55 ) @ ( k2_zfmisc_1 @ X58 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('85',plain,
    ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_2 @ ( k4_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('87',plain,(
    ! [X47: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X47 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('88',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ sk_C_2 @ ( k4_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X45 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X46 @ X45 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('90',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_D_1 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k4_xboole_0 @ sk_D_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k4_xboole_0 @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('93',plain,
    ( ( ( k4_xboole_0 @ sk_D_1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X28: $i] :
      ( ( k4_xboole_0 @ X28 @ k1_xboole_0 )
      = X28 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('95',plain,
    ( ( sk_D_1
      = ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('98',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25 = X24 )
      | ( ( k4_xboole_0 @ X25 @ X24 )
       != ( k4_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('99',plain,
    ( ( ( k4_xboole_0 @ sk_C_2 @ sk_A )
     != k1_xboole_0 )
    | ( sk_C_2 = sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X55 @ X57 ) @ X56 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X55 @ X56 ) @ ( k2_zfmisc_1 @ X57 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X0 @ sk_A ) @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X55: $i,X57: $i,X58: $i] :
      ( ( k2_zfmisc_1 @ X58 @ ( k4_xboole_0 @ X55 @ X57 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X58 @ X55 ) @ ( k2_zfmisc_1 @ X58 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('104',plain,
    ( ( k2_zfmisc_1 @ sk_C_2 @ ( k4_xboole_0 @ sk_B_1 @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_C_2 @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X45 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X46 @ X45 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('106',plain,
    ( ( ( k2_zfmisc_1 @ sk_C_2 @ ( k4_xboole_0 @ sk_B_1 @ sk_D_1 ) )
     != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_C_2 @ sk_A )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( k2_zfmisc_1 @ sk_C_2 @ ( k4_xboole_0 @ sk_B_1 @ sk_D_1 ) )
     != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_C_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','76'])).

thf('110',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k2_zfmisc_1 @ X46 @ X47 )
        = k1_xboole_0 )
      | ( X47 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('111',plain,(
    ! [X46: $i] :
      ( ( k2_zfmisc_1 @ X46 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_C_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['108','109','111'])).

thf('113',plain,
    ( ( k4_xboole_0 @ sk_C_2 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_2 = sk_A ) ),
    inference(demod,[status(thm)],['99','113'])).

thf('115',plain,(
    sk_C_2 = sk_A ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(demod,[status(thm)],['96','115'])).

thf('117',plain,
    ( sk_D_1
    = ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['95','116'])).

thf('118',plain,(
    sk_D_1 = sk_B_1 ),
    inference('sup+',[status(thm)],['82','117'])).

thf('119',plain,
    ( ( sk_A != sk_C_2 )
    | ( sk_B_1 != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( sk_B_1 != sk_D_1 )
   <= ( sk_B_1 != sk_D_1 ) ),
    inference(split,[status(esa)],['119'])).

thf('121',plain,(
    sk_C_2 = sk_A ),
    inference(simplify,[status(thm)],['114'])).

thf('122',plain,
    ( ( sk_A != sk_C_2 )
   <= ( sk_A != sk_C_2 ) ),
    inference(split,[status(esa)],['119'])).

thf('123',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( sk_A != sk_C_2 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    sk_A = sk_C_2 ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( sk_B_1 != sk_D_1 )
    | ( sk_A != sk_C_2 ) ),
    inference(split,[status(esa)],['119'])).

thf('126',plain,(
    sk_B_1 != sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['124','125'])).

thf('127',plain,(
    sk_B_1 != sk_D_1 ),
    inference(simpl_trail,[status(thm)],['120','126'])).

thf('128',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['118','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wxHPwIvWN4
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.07/1.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.07/1.25  % Solved by: fo/fo7.sh
% 1.07/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.25  % done 2003 iterations in 0.804s
% 1.07/1.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.07/1.25  % SZS output start Refutation
% 1.07/1.25  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.07/1.25  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.07/1.25  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.07/1.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.07/1.25  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.07/1.25  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.07/1.25  thf(sk_B_type, type, sk_B: $i > $i).
% 1.07/1.25  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.07/1.25  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.07/1.25  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.07/1.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.07/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.25  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.07/1.25  thf(t36_xboole_1, axiom,
% 1.07/1.25    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.07/1.25  thf('0', plain,
% 1.07/1.25      (![X26 : $i, X27 : $i]: (r1_tarski @ (k4_xboole_0 @ X26 @ X27) @ X26)),
% 1.07/1.25      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.07/1.25  thf(l32_xboole_1, axiom,
% 1.07/1.25    (![A:$i,B:$i]:
% 1.07/1.25     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.07/1.25  thf('1', plain,
% 1.07/1.25      (![X20 : $i, X22 : $i]:
% 1.07/1.25         (((k4_xboole_0 @ X20 @ X22) = (k1_xboole_0))
% 1.07/1.25          | ~ (r1_tarski @ X20 @ X22))),
% 1.07/1.25      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.07/1.25  thf('2', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.07/1.25      inference('sup-', [status(thm)], ['0', '1'])).
% 1.07/1.25  thf(t48_xboole_1, axiom,
% 1.07/1.25    (![A:$i,B:$i]:
% 1.07/1.25     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.07/1.25  thf('3', plain,
% 1.07/1.25      (![X32 : $i, X33 : $i]:
% 1.07/1.25         ((k4_xboole_0 @ X32 @ (k4_xboole_0 @ X32 @ X33))
% 1.07/1.25           = (k3_xboole_0 @ X32 @ X33))),
% 1.07/1.25      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.07/1.25  thf('4', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 1.07/1.25           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.07/1.25      inference('sup+', [status(thm)], ['2', '3'])).
% 1.07/1.25  thf(t3_boole, axiom,
% 1.07/1.25    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.07/1.25  thf('5', plain, (![X28 : $i]: ((k4_xboole_0 @ X28 @ k1_xboole_0) = (X28))),
% 1.07/1.25      inference('cnf', [status(esa)], [t3_boole])).
% 1.07/1.25  thf(commutativity_k3_xboole_0, axiom,
% 1.07/1.25    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.07/1.25  thf('6', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.25      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.25  thf('7', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         ((k4_xboole_0 @ X0 @ X1)
% 1.07/1.25           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.07/1.25      inference('demod', [status(thm)], ['4', '5', '6'])).
% 1.07/1.25  thf(t3_xboole_0, axiom,
% 1.07/1.25    (![A:$i,B:$i]:
% 1.07/1.25     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.07/1.25            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.07/1.25       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.07/1.25            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.07/1.25  thf('8', plain,
% 1.07/1.25      (![X11 : $i, X12 : $i]:
% 1.07/1.25         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X12))),
% 1.07/1.25      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.07/1.25  thf('9', plain,
% 1.07/1.25      (![X11 : $i, X12 : $i]:
% 1.07/1.25         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X11))),
% 1.07/1.25      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.07/1.25  thf(d5_xboole_0, axiom,
% 1.07/1.25    (![A:$i,B:$i,C:$i]:
% 1.07/1.25     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.07/1.25       ( ![D:$i]:
% 1.07/1.25         ( ( r2_hidden @ D @ C ) <=>
% 1.07/1.25           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.07/1.25  thf('10', plain,
% 1.07/1.25      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.07/1.25         (~ (r2_hidden @ X6 @ X5)
% 1.07/1.25          | ~ (r2_hidden @ X6 @ X4)
% 1.07/1.25          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.07/1.25      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.07/1.25  thf('11', plain,
% 1.07/1.25      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.07/1.25         (~ (r2_hidden @ X6 @ X4)
% 1.07/1.25          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.07/1.25      inference('simplify', [status(thm)], ['10'])).
% 1.07/1.25  thf('12', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.25         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 1.07/1.25          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 1.07/1.25      inference('sup-', [status(thm)], ['9', '11'])).
% 1.07/1.25  thf('13', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.07/1.25          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.07/1.25      inference('sup-', [status(thm)], ['8', '12'])).
% 1.07/1.25  thf('14', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 1.07/1.25      inference('simplify', [status(thm)], ['13'])).
% 1.07/1.25  thf(t7_xboole_0, axiom,
% 1.07/1.25    (![A:$i]:
% 1.07/1.25     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.07/1.25          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.07/1.25  thf('15', plain,
% 1.07/1.25      (![X19 : $i]:
% 1.07/1.25         (((X19) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X19) @ X19))),
% 1.07/1.25      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.07/1.25  thf('16', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.25      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.25  thf(t4_xboole_0, axiom,
% 1.07/1.25    (![A:$i,B:$i]:
% 1.07/1.25     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.07/1.25            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.07/1.25       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.07/1.25            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.07/1.25  thf('17', plain,
% 1.07/1.25      (![X15 : $i, X17 : $i, X18 : $i]:
% 1.07/1.25         (~ (r2_hidden @ X17 @ (k3_xboole_0 @ X15 @ X18))
% 1.07/1.25          | ~ (r1_xboole_0 @ X15 @ X18))),
% 1.07/1.25      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.07/1.25  thf('18', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.25         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.07/1.25          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.07/1.25      inference('sup-', [status(thm)], ['16', '17'])).
% 1.07/1.25  thf('19', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.07/1.25      inference('sup-', [status(thm)], ['15', '18'])).
% 1.07/1.25  thf('20', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.07/1.25      inference('sup-', [status(thm)], ['14', '19'])).
% 1.07/1.25  thf(t134_zfmisc_1, conjecture,
% 1.07/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.25     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 1.07/1.25       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.07/1.25         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 1.07/1.25  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.25    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.25        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 1.07/1.25          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.07/1.25            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 1.07/1.25    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 1.07/1.25  thf('21', plain,
% 1.07/1.25      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf(t125_zfmisc_1, axiom,
% 1.07/1.25    (![A:$i,B:$i,C:$i]:
% 1.07/1.25     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 1.07/1.25         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 1.07/1.25       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.07/1.25         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 1.07/1.25  thf('22', plain,
% 1.07/1.25      (![X55 : $i, X56 : $i, X57 : $i]:
% 1.07/1.25         ((k2_zfmisc_1 @ (k4_xboole_0 @ X55 @ X57) @ X56)
% 1.07/1.25           = (k4_xboole_0 @ (k2_zfmisc_1 @ X55 @ X56) @ 
% 1.07/1.25              (k2_zfmisc_1 @ X57 @ X56)))),
% 1.07/1.25      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 1.07/1.25  thf('23', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 1.07/1.25           = (k4_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 1.07/1.25              (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 1.07/1.25      inference('sup+', [status(thm)], ['21', '22'])).
% 1.07/1.25  thf('24', plain,
% 1.07/1.25      (![X32 : $i, X33 : $i]:
% 1.07/1.25         ((k4_xboole_0 @ X32 @ (k4_xboole_0 @ X32 @ X33))
% 1.07/1.25           = (k3_xboole_0 @ X32 @ X33))),
% 1.07/1.25      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.07/1.25  thf('25', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((k4_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 1.07/1.25           (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1))
% 1.07/1.25           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 1.07/1.25              (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 1.07/1.25      inference('sup+', [status(thm)], ['23', '24'])).
% 1.07/1.25  thf('26', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 1.07/1.25           = (k4_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 1.07/1.25              (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 1.07/1.25      inference('sup+', [status(thm)], ['21', '22'])).
% 1.07/1.25  thf('27', plain,
% 1.07/1.25      (![X32 : $i, X33 : $i]:
% 1.07/1.25         ((k4_xboole_0 @ X32 @ (k4_xboole_0 @ X32 @ X33))
% 1.07/1.25           = (k3_xboole_0 @ X32 @ X33))),
% 1.07/1.25      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.07/1.25  thf('28', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 1.07/1.25           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 1.07/1.25              (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 1.07/1.25      inference('demod', [status(thm)], ['25', '26', '27'])).
% 1.07/1.25  thf(t123_zfmisc_1, axiom,
% 1.07/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.25     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 1.07/1.25       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 1.07/1.25  thf('29', plain,
% 1.07/1.25      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 1.07/1.25         ((k2_zfmisc_1 @ (k3_xboole_0 @ X51 @ X53) @ (k3_xboole_0 @ X52 @ X54))
% 1.07/1.25           = (k3_xboole_0 @ (k2_zfmisc_1 @ X51 @ X52) @ 
% 1.07/1.25              (k2_zfmisc_1 @ X53 @ X54)))),
% 1.07/1.25      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 1.07/1.25  thf('30', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 1.07/1.25           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_2 @ X0) @ 
% 1.07/1.25              (k3_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 1.07/1.25      inference('demod', [status(thm)], ['28', '29'])).
% 1.07/1.25  thf('31', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_2)) @ 
% 1.07/1.25           sk_B_1)
% 1.07/1.25           = (k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 1.07/1.25      inference('sup+', [status(thm)], ['20', '30'])).
% 1.07/1.25  thf(t113_zfmisc_1, axiom,
% 1.07/1.25    (![A:$i,B:$i]:
% 1.07/1.25     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.07/1.25       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.07/1.25  thf('32', plain,
% 1.07/1.25      (![X46 : $i, X47 : $i]:
% 1.07/1.25         (((k2_zfmisc_1 @ X46 @ X47) = (k1_xboole_0))
% 1.07/1.25          | ((X46) != (k1_xboole_0)))),
% 1.07/1.25      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.07/1.25  thf('33', plain,
% 1.07/1.25      (![X47 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X47) = (k1_xboole_0))),
% 1.07/1.25      inference('simplify', [status(thm)], ['32'])).
% 1.07/1.25  thf('34', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_2)) @ 
% 1.07/1.25           sk_B_1) = (k1_xboole_0))),
% 1.07/1.25      inference('demod', [status(thm)], ['31', '33'])).
% 1.07/1.25  thf('35', plain,
% 1.07/1.25      (((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C_2) @ sk_B_1) = (k1_xboole_0))),
% 1.07/1.25      inference('sup+', [status(thm)], ['7', '34'])).
% 1.07/1.25  thf('36', plain,
% 1.07/1.25      (![X45 : $i, X46 : $i]:
% 1.07/1.25         (((X45) = (k1_xboole_0))
% 1.07/1.25          | ((X46) = (k1_xboole_0))
% 1.07/1.25          | ((k2_zfmisc_1 @ X46 @ X45) != (k1_xboole_0)))),
% 1.07/1.25      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.07/1.25  thf('37', plain,
% 1.07/1.25      ((((k1_xboole_0) != (k1_xboole_0))
% 1.07/1.25        | ((k4_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0))
% 1.07/1.25        | ((sk_B_1) = (k1_xboole_0)))),
% 1.07/1.25      inference('sup-', [status(thm)], ['35', '36'])).
% 1.07/1.25  thf('38', plain,
% 1.07/1.25      ((((sk_B_1) = (k1_xboole_0))
% 1.07/1.25        | ((k4_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0)))),
% 1.07/1.25      inference('simplify', [status(thm)], ['37'])).
% 1.07/1.25  thf('39', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('40', plain, (((k4_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0))),
% 1.07/1.25      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 1.07/1.25  thf('41', plain,
% 1.07/1.25      (![X32 : $i, X33 : $i]:
% 1.07/1.25         ((k4_xboole_0 @ X32 @ (k4_xboole_0 @ X32 @ X33))
% 1.07/1.25           = (k3_xboole_0 @ X32 @ X33))),
% 1.07/1.25      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.07/1.25  thf('42', plain,
% 1.07/1.25      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C_2))),
% 1.07/1.25      inference('sup+', [status(thm)], ['40', '41'])).
% 1.07/1.25  thf('43', plain, (![X28 : $i]: ((k4_xboole_0 @ X28 @ k1_xboole_0) = (X28))),
% 1.07/1.25      inference('cnf', [status(esa)], [t3_boole])).
% 1.07/1.25  thf('44', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.25      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.25  thf('45', plain, (((sk_A) = (k3_xboole_0 @ sk_C_2 @ sk_A))),
% 1.07/1.25      inference('demod', [status(thm)], ['42', '43', '44'])).
% 1.07/1.25  thf('46', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 1.07/1.25           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_2 @ X0) @ 
% 1.07/1.25              (k3_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 1.07/1.25      inference('demod', [status(thm)], ['28', '29'])).
% 1.07/1.25  thf('47', plain,
% 1.07/1.25      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_A) @ sk_B_1)
% 1.07/1.25         = (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 1.07/1.25      inference('sup+', [status(thm)], ['45', '46'])).
% 1.07/1.25  thf('48', plain, (![X28 : $i]: ((k4_xboole_0 @ X28 @ k1_xboole_0) = (X28))),
% 1.07/1.25      inference('cnf', [status(esa)], [t3_boole])).
% 1.07/1.25  thf('49', plain,
% 1.07/1.25      (![X26 : $i, X27 : $i]: (r1_tarski @ (k4_xboole_0 @ X26 @ X27) @ X26)),
% 1.07/1.25      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.07/1.25  thf('50', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.07/1.25      inference('sup+', [status(thm)], ['48', '49'])).
% 1.07/1.25  thf('51', plain,
% 1.07/1.25      (![X20 : $i, X22 : $i]:
% 1.07/1.25         (((k4_xboole_0 @ X20 @ X22) = (k1_xboole_0))
% 1.07/1.25          | ~ (r1_tarski @ X20 @ X22))),
% 1.07/1.25      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.07/1.25  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.07/1.25      inference('sup-', [status(thm)], ['50', '51'])).
% 1.07/1.25  thf('53', plain,
% 1.07/1.25      (![X32 : $i, X33 : $i]:
% 1.07/1.25         ((k4_xboole_0 @ X32 @ (k4_xboole_0 @ X32 @ X33))
% 1.07/1.25           = (k3_xboole_0 @ X32 @ X33))),
% 1.07/1.25      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.07/1.25  thf('54', plain,
% 1.07/1.25      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.07/1.25      inference('sup+', [status(thm)], ['52', '53'])).
% 1.07/1.25  thf('55', plain, (![X28 : $i]: ((k4_xboole_0 @ X28 @ k1_xboole_0) = (X28))),
% 1.07/1.25      inference('cnf', [status(esa)], [t3_boole])).
% 1.07/1.25  thf('56', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.07/1.25      inference('demod', [status(thm)], ['54', '55'])).
% 1.07/1.25  thf('57', plain,
% 1.07/1.25      (((k2_zfmisc_1 @ sk_A @ sk_B_1)
% 1.07/1.25         = (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 1.07/1.25      inference('demod', [status(thm)], ['47', '56'])).
% 1.07/1.25  thf('58', plain,
% 1.07/1.25      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('59', plain,
% 1.07/1.25      (((k2_zfmisc_1 @ sk_C_2 @ sk_D_1)
% 1.07/1.25         = (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 1.07/1.25      inference('demod', [status(thm)], ['57', '58'])).
% 1.07/1.25  thf('60', plain,
% 1.07/1.25      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf(t117_zfmisc_1, axiom,
% 1.07/1.25    (![A:$i,B:$i,C:$i]:
% 1.07/1.25     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.07/1.25          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 1.07/1.25            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 1.07/1.25          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 1.07/1.25  thf('61', plain,
% 1.07/1.25      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.07/1.25         (((X48) = (k1_xboole_0))
% 1.07/1.25          | (r1_tarski @ X49 @ X50)
% 1.07/1.25          | ~ (r1_tarski @ (k2_zfmisc_1 @ X48 @ X49) @ 
% 1.07/1.25               (k2_zfmisc_1 @ X48 @ X50)))),
% 1.07/1.25      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 1.07/1.25  thf('62', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 1.07/1.25             (k2_zfmisc_1 @ sk_A @ X0))
% 1.07/1.25          | (r1_tarski @ sk_B_1 @ X0)
% 1.07/1.25          | ((sk_A) = (k1_xboole_0)))),
% 1.07/1.25      inference('sup-', [status(thm)], ['60', '61'])).
% 1.07/1.25  thf('63', plain, (((sk_A) != (k1_xboole_0))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('64', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 1.07/1.25             (k2_zfmisc_1 @ sk_A @ X0))
% 1.07/1.25          | (r1_tarski @ sk_B_1 @ X0))),
% 1.07/1.25      inference('simplify_reflect-', [status(thm)], ['62', '63'])).
% 1.07/1.25  thf('65', plain,
% 1.07/1.25      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 1.07/1.25           (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 1.07/1.25        | (r1_tarski @ sk_B_1 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 1.07/1.25      inference('sup-', [status(thm)], ['59', '64'])).
% 1.07/1.25  thf('66', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.07/1.25      inference('sup+', [status(thm)], ['48', '49'])).
% 1.07/1.25  thf('67', plain, ((r1_tarski @ sk_B_1 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1))),
% 1.07/1.25      inference('demod', [status(thm)], ['65', '66'])).
% 1.07/1.25  thf('68', plain,
% 1.07/1.25      (![X20 : $i, X22 : $i]:
% 1.07/1.25         (((k4_xboole_0 @ X20 @ X22) = (k1_xboole_0))
% 1.07/1.25          | ~ (r1_tarski @ X20 @ X22))),
% 1.07/1.25      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.07/1.25  thf('69', plain,
% 1.07/1.25      (((k4_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1))
% 1.07/1.25         = (k1_xboole_0))),
% 1.07/1.25      inference('sup-', [status(thm)], ['67', '68'])).
% 1.07/1.25  thf('70', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.25      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.25  thf('71', plain,
% 1.07/1.25      (![X32 : $i, X33 : $i]:
% 1.07/1.25         ((k4_xboole_0 @ X32 @ (k4_xboole_0 @ X32 @ X33))
% 1.07/1.25           = (k3_xboole_0 @ X32 @ X33))),
% 1.07/1.25      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.07/1.25  thf('72', plain,
% 1.07/1.25      (![X32 : $i, X33 : $i]:
% 1.07/1.25         ((k4_xboole_0 @ X32 @ (k4_xboole_0 @ X32 @ X33))
% 1.07/1.25           = (k3_xboole_0 @ X32 @ X33))),
% 1.07/1.25      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.07/1.25  thf('73', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.07/1.25           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.07/1.25      inference('sup+', [status(thm)], ['71', '72'])).
% 1.07/1.25  thf('74', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         ((k4_xboole_0 @ X0 @ X1)
% 1.07/1.25           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.07/1.25      inference('demod', [status(thm)], ['4', '5', '6'])).
% 1.07/1.25  thf('75', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.07/1.25           = (k4_xboole_0 @ X1 @ X0))),
% 1.07/1.25      inference('demod', [status(thm)], ['73', '74'])).
% 1.07/1.25  thf('76', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.07/1.25           = (k4_xboole_0 @ X0 @ X1))),
% 1.07/1.25      inference('sup+', [status(thm)], ['70', '75'])).
% 1.07/1.25  thf('77', plain, (((k4_xboole_0 @ sk_B_1 @ sk_D_1) = (k1_xboole_0))),
% 1.07/1.25      inference('demod', [status(thm)], ['69', '76'])).
% 1.07/1.25  thf('78', plain,
% 1.07/1.25      (![X32 : $i, X33 : $i]:
% 1.07/1.25         ((k4_xboole_0 @ X32 @ (k4_xboole_0 @ X32 @ X33))
% 1.07/1.25           = (k3_xboole_0 @ X32 @ X33))),
% 1.07/1.25      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.07/1.25  thf('79', plain,
% 1.07/1.25      (((k4_xboole_0 @ sk_B_1 @ k1_xboole_0) = (k3_xboole_0 @ sk_B_1 @ sk_D_1))),
% 1.07/1.25      inference('sup+', [status(thm)], ['77', '78'])).
% 1.07/1.25  thf('80', plain, (![X28 : $i]: ((k4_xboole_0 @ X28 @ k1_xboole_0) = (X28))),
% 1.07/1.25      inference('cnf', [status(esa)], [t3_boole])).
% 1.07/1.25  thf('81', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.25      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.25  thf('82', plain, (((sk_B_1) = (k3_xboole_0 @ sk_D_1 @ sk_B_1))),
% 1.07/1.25      inference('demod', [status(thm)], ['79', '80', '81'])).
% 1.07/1.25  thf('83', plain,
% 1.07/1.25      (![X55 : $i, X57 : $i, X58 : $i]:
% 1.07/1.25         ((k2_zfmisc_1 @ X58 @ (k4_xboole_0 @ X55 @ X57))
% 1.07/1.25           = (k4_xboole_0 @ (k2_zfmisc_1 @ X58 @ X55) @ 
% 1.07/1.25              (k2_zfmisc_1 @ X58 @ X57)))),
% 1.07/1.25      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 1.07/1.25  thf('84', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 1.07/1.25           = (k4_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 1.07/1.25              (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 1.07/1.25      inference('sup+', [status(thm)], ['21', '22'])).
% 1.07/1.25  thf('85', plain,
% 1.07/1.25      (((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C_2) @ sk_B_1)
% 1.07/1.25         = (k2_zfmisc_1 @ sk_C_2 @ (k4_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 1.07/1.25      inference('sup+', [status(thm)], ['83', '84'])).
% 1.07/1.25  thf('86', plain, (((k4_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0))),
% 1.07/1.25      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 1.07/1.25  thf('87', plain,
% 1.07/1.25      (![X47 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X47) = (k1_xboole_0))),
% 1.07/1.25      inference('simplify', [status(thm)], ['32'])).
% 1.07/1.25  thf('88', plain,
% 1.07/1.25      (((k1_xboole_0)
% 1.07/1.25         = (k2_zfmisc_1 @ sk_C_2 @ (k4_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 1.07/1.25      inference('demod', [status(thm)], ['85', '86', '87'])).
% 1.07/1.25  thf('89', plain,
% 1.07/1.25      (![X45 : $i, X46 : $i]:
% 1.07/1.25         (((X45) = (k1_xboole_0))
% 1.07/1.25          | ((X46) = (k1_xboole_0))
% 1.07/1.25          | ((k2_zfmisc_1 @ X46 @ X45) != (k1_xboole_0)))),
% 1.07/1.25      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.07/1.25  thf('90', plain,
% 1.07/1.25      ((((k1_xboole_0) != (k1_xboole_0))
% 1.07/1.25        | ((sk_C_2) = (k1_xboole_0))
% 1.07/1.25        | ((k4_xboole_0 @ sk_D_1 @ sk_B_1) = (k1_xboole_0)))),
% 1.07/1.25      inference('sup-', [status(thm)], ['88', '89'])).
% 1.07/1.25  thf('91', plain,
% 1.07/1.25      ((((k4_xboole_0 @ sk_D_1 @ sk_B_1) = (k1_xboole_0))
% 1.07/1.25        | ((sk_C_2) = (k1_xboole_0)))),
% 1.07/1.25      inference('simplify', [status(thm)], ['90'])).
% 1.07/1.25  thf('92', plain,
% 1.07/1.25      (![X32 : $i, X33 : $i]:
% 1.07/1.25         ((k4_xboole_0 @ X32 @ (k4_xboole_0 @ X32 @ X33))
% 1.07/1.25           = (k3_xboole_0 @ X32 @ X33))),
% 1.07/1.25      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.07/1.25  thf('93', plain,
% 1.07/1.25      ((((k4_xboole_0 @ sk_D_1 @ k1_xboole_0) = (k3_xboole_0 @ sk_D_1 @ sk_B_1))
% 1.07/1.25        | ((sk_C_2) = (k1_xboole_0)))),
% 1.07/1.25      inference('sup+', [status(thm)], ['91', '92'])).
% 1.07/1.25  thf('94', plain, (![X28 : $i]: ((k4_xboole_0 @ X28 @ k1_xboole_0) = (X28))),
% 1.07/1.25      inference('cnf', [status(esa)], [t3_boole])).
% 1.07/1.25  thf('95', plain,
% 1.07/1.25      ((((sk_D_1) = (k3_xboole_0 @ sk_D_1 @ sk_B_1))
% 1.07/1.25        | ((sk_C_2) = (k1_xboole_0)))),
% 1.07/1.25      inference('demod', [status(thm)], ['93', '94'])).
% 1.07/1.25  thf('96', plain, (((sk_A) != (k1_xboole_0))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('97', plain, (((k4_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0))),
% 1.07/1.25      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 1.07/1.25  thf(t32_xboole_1, axiom,
% 1.07/1.25    (![A:$i,B:$i]:
% 1.07/1.25     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 1.07/1.25       ( ( A ) = ( B ) ) ))).
% 1.07/1.25  thf('98', plain,
% 1.07/1.25      (![X24 : $i, X25 : $i]:
% 1.07/1.25         (((X25) = (X24))
% 1.07/1.25          | ((k4_xboole_0 @ X25 @ X24) != (k4_xboole_0 @ X24 @ X25)))),
% 1.07/1.25      inference('cnf', [status(esa)], [t32_xboole_1])).
% 1.07/1.25  thf('99', plain,
% 1.07/1.25      ((((k4_xboole_0 @ sk_C_2 @ sk_A) != (k1_xboole_0)) | ((sk_C_2) = (sk_A)))),
% 1.07/1.25      inference('sup-', [status(thm)], ['97', '98'])).
% 1.07/1.25  thf('100', plain,
% 1.07/1.25      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('101', plain,
% 1.07/1.25      (![X55 : $i, X56 : $i, X57 : $i]:
% 1.07/1.25         ((k2_zfmisc_1 @ (k4_xboole_0 @ X55 @ X57) @ X56)
% 1.07/1.25           = (k4_xboole_0 @ (k2_zfmisc_1 @ X55 @ X56) @ 
% 1.07/1.25              (k2_zfmisc_1 @ X57 @ X56)))),
% 1.07/1.25      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 1.07/1.25  thf('102', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((k2_zfmisc_1 @ (k4_xboole_0 @ X0 @ sk_A) @ sk_B_1)
% 1.07/1.25           = (k4_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_B_1) @ 
% 1.07/1.25              (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)))),
% 1.07/1.25      inference('sup+', [status(thm)], ['100', '101'])).
% 1.07/1.25  thf('103', plain,
% 1.07/1.25      (![X55 : $i, X57 : $i, X58 : $i]:
% 1.07/1.25         ((k2_zfmisc_1 @ X58 @ (k4_xboole_0 @ X55 @ X57))
% 1.07/1.25           = (k4_xboole_0 @ (k2_zfmisc_1 @ X58 @ X55) @ 
% 1.07/1.25              (k2_zfmisc_1 @ X58 @ X57)))),
% 1.07/1.25      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 1.07/1.25  thf('104', plain,
% 1.07/1.25      (((k2_zfmisc_1 @ sk_C_2 @ (k4_xboole_0 @ sk_B_1 @ sk_D_1))
% 1.07/1.25         = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_C_2 @ sk_A) @ sk_B_1))),
% 1.07/1.25      inference('sup+', [status(thm)], ['102', '103'])).
% 1.07/1.25  thf('105', plain,
% 1.07/1.25      (![X45 : $i, X46 : $i]:
% 1.07/1.25         (((X45) = (k1_xboole_0))
% 1.07/1.25          | ((X46) = (k1_xboole_0))
% 1.07/1.25          | ((k2_zfmisc_1 @ X46 @ X45) != (k1_xboole_0)))),
% 1.07/1.25      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.07/1.25  thf('106', plain,
% 1.07/1.25      ((((k2_zfmisc_1 @ sk_C_2 @ (k4_xboole_0 @ sk_B_1 @ sk_D_1))
% 1.07/1.25          != (k1_xboole_0))
% 1.07/1.25        | ((k4_xboole_0 @ sk_C_2 @ sk_A) = (k1_xboole_0))
% 1.07/1.25        | ((sk_B_1) = (k1_xboole_0)))),
% 1.07/1.25      inference('sup-', [status(thm)], ['104', '105'])).
% 1.07/1.25  thf('107', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('108', plain,
% 1.07/1.25      ((((k2_zfmisc_1 @ sk_C_2 @ (k4_xboole_0 @ sk_B_1 @ sk_D_1))
% 1.07/1.25          != (k1_xboole_0))
% 1.07/1.25        | ((k4_xboole_0 @ sk_C_2 @ sk_A) = (k1_xboole_0)))),
% 1.07/1.25      inference('simplify_reflect-', [status(thm)], ['106', '107'])).
% 1.07/1.25  thf('109', plain, (((k4_xboole_0 @ sk_B_1 @ sk_D_1) = (k1_xboole_0))),
% 1.07/1.25      inference('demod', [status(thm)], ['69', '76'])).
% 1.07/1.25  thf('110', plain,
% 1.07/1.25      (![X46 : $i, X47 : $i]:
% 1.07/1.25         (((k2_zfmisc_1 @ X46 @ X47) = (k1_xboole_0))
% 1.07/1.25          | ((X47) != (k1_xboole_0)))),
% 1.07/1.25      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.07/1.25  thf('111', plain,
% 1.07/1.25      (![X46 : $i]: ((k2_zfmisc_1 @ X46 @ k1_xboole_0) = (k1_xboole_0))),
% 1.07/1.25      inference('simplify', [status(thm)], ['110'])).
% 1.07/1.25  thf('112', plain,
% 1.07/1.25      ((((k1_xboole_0) != (k1_xboole_0))
% 1.07/1.25        | ((k4_xboole_0 @ sk_C_2 @ sk_A) = (k1_xboole_0)))),
% 1.07/1.25      inference('demod', [status(thm)], ['108', '109', '111'])).
% 1.07/1.25  thf('113', plain, (((k4_xboole_0 @ sk_C_2 @ sk_A) = (k1_xboole_0))),
% 1.07/1.25      inference('simplify', [status(thm)], ['112'])).
% 1.07/1.25  thf('114', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_2) = (sk_A)))),
% 1.07/1.25      inference('demod', [status(thm)], ['99', '113'])).
% 1.07/1.25  thf('115', plain, (((sk_C_2) = (sk_A))),
% 1.07/1.25      inference('simplify', [status(thm)], ['114'])).
% 1.07/1.25  thf('116', plain, (((sk_C_2) != (k1_xboole_0))),
% 1.07/1.25      inference('demod', [status(thm)], ['96', '115'])).
% 1.07/1.25  thf('117', plain, (((sk_D_1) = (k3_xboole_0 @ sk_D_1 @ sk_B_1))),
% 1.07/1.25      inference('simplify_reflect-', [status(thm)], ['95', '116'])).
% 1.07/1.25  thf('118', plain, (((sk_D_1) = (sk_B_1))),
% 1.07/1.25      inference('sup+', [status(thm)], ['82', '117'])).
% 1.07/1.25  thf('119', plain, ((((sk_A) != (sk_C_2)) | ((sk_B_1) != (sk_D_1)))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('120', plain, ((((sk_B_1) != (sk_D_1))) <= (~ (((sk_B_1) = (sk_D_1))))),
% 1.07/1.25      inference('split', [status(esa)], ['119'])).
% 1.07/1.25  thf('121', plain, (((sk_C_2) = (sk_A))),
% 1.07/1.25      inference('simplify', [status(thm)], ['114'])).
% 1.07/1.25  thf('122', plain, ((((sk_A) != (sk_C_2))) <= (~ (((sk_A) = (sk_C_2))))),
% 1.07/1.25      inference('split', [status(esa)], ['119'])).
% 1.07/1.25  thf('123', plain, ((((sk_C_2) != (sk_C_2))) <= (~ (((sk_A) = (sk_C_2))))),
% 1.07/1.25      inference('sup-', [status(thm)], ['121', '122'])).
% 1.07/1.25  thf('124', plain, ((((sk_A) = (sk_C_2)))),
% 1.07/1.25      inference('simplify', [status(thm)], ['123'])).
% 1.07/1.25  thf('125', plain, (~ (((sk_B_1) = (sk_D_1))) | ~ (((sk_A) = (sk_C_2)))),
% 1.07/1.25      inference('split', [status(esa)], ['119'])).
% 1.07/1.25  thf('126', plain, (~ (((sk_B_1) = (sk_D_1)))),
% 1.07/1.25      inference('sat_resolution*', [status(thm)], ['124', '125'])).
% 1.07/1.25  thf('127', plain, (((sk_B_1) != (sk_D_1))),
% 1.07/1.25      inference('simpl_trail', [status(thm)], ['120', '126'])).
% 1.07/1.25  thf('128', plain, ($false),
% 1.07/1.25      inference('simplify_reflect-', [status(thm)], ['118', '127'])).
% 1.07/1.25  
% 1.07/1.25  % SZS output end Refutation
% 1.07/1.25  
% 1.07/1.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

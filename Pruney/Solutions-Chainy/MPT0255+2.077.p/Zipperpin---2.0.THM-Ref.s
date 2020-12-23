%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CwZXQQKYFH

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:05 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  110 (3164 expanded)
%              Number of leaves         :   18 ( 921 expanded)
%              Depth                    :   33
%              Number of atoms          : 1363 (43395 expanded)
%              Number of equality atoms :   73 (1784 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('7',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ sk_C_1 )
      | ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ sk_C_1 )
      | ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ sk_C_1 )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( X0
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('14',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

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

thf('15',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X1 )
      | ( X2
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ sk_C_1 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( X0
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('21',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ sk_C_1 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ sk_C_1 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X1 )
      | ( X2
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( X0
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('37',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['9','37'])).

thf('39',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ sk_C_1 )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(eq_fact,[status(thm)],['38'])).

thf('40',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('41',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X1 )
      | ( X2
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ sk_C_1 )
    | ~ ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( k1_xboole_0
      = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('46',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('47',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('56',plain,
    ( ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ sk_C_1 )
    | ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','54','55'])).

thf('57',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ sk_C_1 )
    | ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ sk_C_1 )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(eq_fact,[status(thm)],['38'])).

thf('59',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('60',plain,
    ( ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ sk_C_1 )
    | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('62',plain,
    ( ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ sk_C_1 )
    | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ sk_C_1 )
    | ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['57','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X1 )
      | ( X2
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('66',plain,
    ( ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B ) )
    | ~ ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ( k1_xboole_0
      = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('68',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('69',plain,
    ( ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B ) )
    | ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('72',plain,
    ( ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('74',plain,
    ( ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('77',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( k1_xboole_0
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['75','80'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('82',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ ( k2_tarski @ X21 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('84',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_xboole_0 @ X0 @ X1 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CwZXQQKYFH
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:28:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.84/1.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.84/1.06  % Solved by: fo/fo7.sh
% 0.84/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.06  % done 935 iterations in 0.603s
% 0.84/1.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.84/1.06  % SZS output start Refutation
% 0.84/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.06  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.84/1.06  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.84/1.06  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.84/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.84/1.06  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.84/1.06  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.84/1.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.06  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.84/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.06  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.84/1.06  thf('0', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 0.84/1.06      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.84/1.06  thf(d3_xboole_0, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.84/1.06       ( ![D:$i]:
% 0.84/1.06         ( ( r2_hidden @ D @ C ) <=>
% 0.84/1.06           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.84/1.06  thf('1', plain,
% 0.84/1.06      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.84/1.06         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.84/1.06          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.84/1.06          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 0.84/1.06          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.84/1.06      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.84/1.06  thf('2', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.84/1.06          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.84/1.06          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.84/1.06      inference('eq_fact', [status(thm)], ['1'])).
% 0.84/1.06  thf(t50_zfmisc_1, conjecture,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.84/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.06    (~( ![A:$i,B:$i,C:$i]:
% 0.84/1.06        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.84/1.06    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.84/1.06  thf('3', plain,
% 0.84/1.06      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf(commutativity_k2_xboole_0, axiom,
% 0.84/1.06    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.84/1.06  thf('4', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.84/1.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.84/1.06  thf('5', plain,
% 0.84/1.06      (((k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.84/1.06      inference('demod', [status(thm)], ['3', '4'])).
% 0.84/1.06  thf('6', plain,
% 0.84/1.06      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X6 @ X4)
% 0.84/1.06          | (r2_hidden @ X6 @ X5)
% 0.84/1.06          | (r2_hidden @ X6 @ X3)
% 0.84/1.06          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.84/1.06      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.84/1.06  thf('7', plain,
% 0.84/1.06      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.84/1.06         ((r2_hidden @ X6 @ X3)
% 0.84/1.06          | (r2_hidden @ X6 @ X5)
% 0.84/1.06          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 0.84/1.06      inference('simplify', [status(thm)], ['6'])).
% 0.84/1.06  thf('8', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.84/1.06          | (r2_hidden @ X0 @ sk_C_1)
% 0.84/1.06          | (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['5', '7'])).
% 0.84/1.06  thf('9', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (((k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.84/1.06          | (r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0) @ X0)
% 0.84/1.06          | (r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0) @ 
% 0.84/1.06             (k2_tarski @ sk_A @ sk_B))
% 0.84/1.06          | (r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0) @ sk_C_1))),
% 0.84/1.06      inference('sup-', [status(thm)], ['2', '8'])).
% 0.84/1.06  thf('10', plain,
% 0.84/1.06      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.84/1.06         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.84/1.06          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.84/1.06          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 0.84/1.06          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.84/1.06      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.84/1.06  thf('11', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.84/1.06          | (r2_hidden @ X0 @ sk_C_1)
% 0.84/1.06          | (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['5', '7'])).
% 0.84/1.06  thf('12', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.84/1.06          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X0)
% 0.84/1.06          | ((X1) = (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.84/1.06          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ 
% 0.84/1.06             (k2_tarski @ sk_A @ sk_B))
% 0.84/1.06          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ sk_C_1))),
% 0.84/1.06      inference('sup-', [status(thm)], ['10', '11'])).
% 0.84/1.06  thf('13', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ sk_C_1)
% 0.84/1.06          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ 
% 0.84/1.06             (k2_tarski @ sk_A @ sk_B))
% 0.84/1.06          | ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.84/1.06          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ X0))),
% 0.84/1.06      inference('eq_fact', [status(thm)], ['12'])).
% 0.84/1.06  thf('14', plain,
% 0.84/1.06      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.84/1.06         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.84/1.06          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.84/1.06          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 0.84/1.06          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.84/1.06      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.84/1.06  thf(t3_xboole_0, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.84/1.06            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.84/1.06       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.84/1.06            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.84/1.06  thf('15', plain,
% 0.84/1.06      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X10 @ X8)
% 0.84/1.06          | ~ (r2_hidden @ X10 @ X11)
% 0.84/1.06          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.84/1.06      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.84/1.06  thf('16', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.06         ((r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ X2)
% 0.84/1.06          | (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ X1)
% 0.84/1.06          | ((X2) = (k2_xboole_0 @ X1 @ X0))
% 0.84/1.06          | ~ (r1_xboole_0 @ X0 @ X3)
% 0.84/1.06          | ~ (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ X3))),
% 0.84/1.06      inference('sup-', [status(thm)], ['14', '15'])).
% 0.84/1.06  thf('17', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ X0)
% 0.84/1.06          | ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.84/1.06          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ sk_C_1)
% 0.84/1.06          | ~ (r1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B))
% 0.84/1.06          | ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.84/1.06          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ X0)
% 0.84/1.06          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['13', '16'])).
% 0.84/1.06  thf('18', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 0.84/1.06      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.84/1.06  thf('19', plain,
% 0.84/1.06      (![X8 : $i, X9 : $i]:
% 0.84/1.06         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.84/1.06      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.84/1.06  thf('20', plain,
% 0.84/1.06      (![X8 : $i, X9 : $i]:
% 0.84/1.06         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.84/1.06      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.84/1.06  thf('21', plain,
% 0.84/1.06      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X10 @ X8)
% 0.84/1.06          | ~ (r2_hidden @ X10 @ X11)
% 0.84/1.06          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.84/1.06      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.84/1.06  thf('22', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.06         ((r1_xboole_0 @ X0 @ X1)
% 0.84/1.06          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.84/1.06          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.84/1.06      inference('sup-', [status(thm)], ['20', '21'])).
% 0.84/1.06  thf('23', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((r1_xboole_0 @ X0 @ X1)
% 0.84/1.06          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.84/1.06          | (r1_xboole_0 @ X0 @ X1))),
% 0.84/1.06      inference('sup-', [status(thm)], ['19', '22'])).
% 0.84/1.06  thf('24', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.84/1.06      inference('simplify', [status(thm)], ['23'])).
% 0.84/1.06  thf('25', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.84/1.06      inference('sup-', [status(thm)], ['18', '24'])).
% 0.84/1.06  thf('26', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ X0)
% 0.84/1.06          | ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.84/1.06          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ sk_C_1)
% 0.84/1.06          | ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.84/1.06          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ X0)
% 0.84/1.06          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ X0))),
% 0.84/1.06      inference('demod', [status(thm)], ['17', '25'])).
% 0.84/1.06  thf('27', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ sk_C_1)
% 0.84/1.06          | ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.84/1.06          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ X0))),
% 0.84/1.06      inference('simplify', [status(thm)], ['26'])).
% 0.84/1.06  thf('28', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.06         ((r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ X2)
% 0.84/1.06          | (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ X1)
% 0.84/1.06          | ((X2) = (k2_xboole_0 @ X1 @ X0))
% 0.84/1.06          | ~ (r1_xboole_0 @ X0 @ X3)
% 0.84/1.06          | ~ (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ X3))),
% 0.84/1.06      inference('sup-', [status(thm)], ['14', '15'])).
% 0.84/1.06  thf('29', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ X0)
% 0.84/1.06          | ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.84/1.06          | ~ (r1_xboole_0 @ k1_xboole_0 @ sk_C_1)
% 0.84/1.06          | ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.84/1.06          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ X0)
% 0.84/1.06          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['27', '28'])).
% 0.84/1.06  thf('30', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.84/1.06      inference('sup-', [status(thm)], ['18', '24'])).
% 0.84/1.06  thf('31', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ X0)
% 0.84/1.06          | ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.84/1.06          | ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.84/1.06          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ X0)
% 0.84/1.06          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ X0))),
% 0.84/1.06      inference('demod', [status(thm)], ['29', '30'])).
% 0.84/1.06  thf('32', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.84/1.06          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ X0))),
% 0.84/1.06      inference('simplify', [status(thm)], ['31'])).
% 0.84/1.06  thf('33', plain,
% 0.84/1.06      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.84/1.06         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.84/1.06          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 0.84/1.06          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.84/1.06      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.84/1.06  thf('34', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.84/1.06          | ~ (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ X0)
% 0.84/1.06          | ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['32', '33'])).
% 0.84/1.06  thf('35', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (~ (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ X0)
% 0.84/1.06          | ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.84/1.06      inference('simplify', [status(thm)], ['34'])).
% 0.84/1.06  thf('36', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.84/1.06          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X0) @ X0))),
% 0.84/1.06      inference('simplify', [status(thm)], ['31'])).
% 0.84/1.06  thf('37', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.84/1.06      inference('clc', [status(thm)], ['35', '36'])).
% 0.84/1.06  thf('38', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (((k1_xboole_0) = (X0))
% 0.84/1.06          | (r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0) @ X0)
% 0.84/1.06          | (r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0) @ 
% 0.84/1.06             (k2_tarski @ sk_A @ sk_B))
% 0.84/1.06          | (r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0) @ sk_C_1))),
% 0.84/1.06      inference('demod', [status(thm)], ['9', '37'])).
% 0.84/1.06  thf('39', plain,
% 0.84/1.06      (((r2_hidden @ 
% 0.84/1.06         (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06         sk_C_1)
% 0.84/1.06        | (r2_hidden @ 
% 0.84/1.06           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06           (k2_tarski @ sk_A @ sk_B))
% 0.84/1.06        | ((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B)))),
% 0.84/1.06      inference('eq_fact', [status(thm)], ['38'])).
% 0.84/1.06  thf('40', plain,
% 0.84/1.06      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.84/1.06         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.84/1.06          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.84/1.06          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 0.84/1.06          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.84/1.06      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.84/1.06  thf('41', plain,
% 0.84/1.06      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X10 @ X8)
% 0.84/1.06          | ~ (r2_hidden @ X10 @ X11)
% 0.84/1.06          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.84/1.06      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.84/1.06  thf('42', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.06         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.84/1.06          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X1)
% 0.84/1.06          | ((X2) = (k2_xboole_0 @ X0 @ X1))
% 0.84/1.06          | ~ (r1_xboole_0 @ X0 @ X3)
% 0.84/1.06          | ~ (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X3))),
% 0.84/1.06      inference('sup-', [status(thm)], ['40', '41'])).
% 0.84/1.06  thf('43', plain,
% 0.84/1.06      ((((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))
% 0.84/1.06        | (r2_hidden @ 
% 0.84/1.06           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06           sk_C_1)
% 0.84/1.06        | ~ (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.84/1.06             (k2_tarski @ sk_A @ sk_B))
% 0.84/1.06        | ((k1_xboole_0)
% 0.84/1.06            = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0))
% 0.84/1.06        | (r2_hidden @ 
% 0.84/1.06           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06           k1_xboole_0)
% 0.84/1.06        | (r2_hidden @ 
% 0.84/1.06           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06           k1_xboole_0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['39', '42'])).
% 0.84/1.06  thf('44', plain,
% 0.84/1.06      (((k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.84/1.06      inference('demod', [status(thm)], ['3', '4'])).
% 0.84/1.06  thf('45', plain,
% 0.84/1.06      (![X8 : $i, X9 : $i]:
% 0.84/1.06         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.84/1.06      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.84/1.06  thf('46', plain,
% 0.84/1.06      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X2 @ X3)
% 0.84/1.06          | (r2_hidden @ X2 @ X4)
% 0.84/1.06          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.84/1.06      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.84/1.06  thf('47', plain,
% 0.84/1.06      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.84/1.06         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.84/1.06      inference('simplify', [status(thm)], ['46'])).
% 0.84/1.06  thf('48', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.06         ((r1_xboole_0 @ X0 @ X1)
% 0.84/1.06          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['45', '47'])).
% 0.84/1.06  thf('49', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.06         ((r1_xboole_0 @ X0 @ X1)
% 0.84/1.06          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.84/1.06          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.84/1.06      inference('sup-', [status(thm)], ['20', '21'])).
% 0.84/1.06  thf('50', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.06         ((r1_xboole_0 @ X0 @ X2)
% 0.84/1.06          | ~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.84/1.06          | (r1_xboole_0 @ X0 @ X2))),
% 0.84/1.06      inference('sup-', [status(thm)], ['48', '49'])).
% 0.84/1.06  thf('51', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.06         (~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.84/1.06          | (r1_xboole_0 @ X0 @ X2))),
% 0.84/1.06      inference('simplify', [status(thm)], ['50'])).
% 0.84/1.06  thf('52', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (~ (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0)
% 0.84/1.06          | (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['44', '51'])).
% 0.84/1.06  thf('53', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 0.84/1.06      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.84/1.06  thf('54', plain,
% 0.84/1.06      (![X0 : $i]: (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)),
% 0.84/1.06      inference('demod', [status(thm)], ['52', '53'])).
% 0.84/1.06  thf('55', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.84/1.06      inference('clc', [status(thm)], ['35', '36'])).
% 0.84/1.06  thf('56', plain,
% 0.84/1.06      ((((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))
% 0.84/1.06        | (r2_hidden @ 
% 0.84/1.06           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06           sk_C_1)
% 0.84/1.06        | ((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))
% 0.84/1.06        | (r2_hidden @ 
% 0.84/1.06           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06           k1_xboole_0)
% 0.84/1.06        | (r2_hidden @ 
% 0.84/1.06           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06           k1_xboole_0))),
% 0.84/1.06      inference('demod', [status(thm)], ['43', '54', '55'])).
% 0.84/1.06  thf('57', plain,
% 0.84/1.06      (((r2_hidden @ 
% 0.84/1.06         (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06         k1_xboole_0)
% 0.84/1.06        | (r2_hidden @ 
% 0.84/1.06           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06           sk_C_1)
% 0.84/1.06        | ((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B)))),
% 0.84/1.06      inference('simplify', [status(thm)], ['56'])).
% 0.84/1.06  thf('58', plain,
% 0.84/1.06      (((r2_hidden @ 
% 0.84/1.06         (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06         sk_C_1)
% 0.84/1.06        | (r2_hidden @ 
% 0.84/1.06           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06           (k2_tarski @ sk_A @ sk_B))
% 0.84/1.06        | ((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B)))),
% 0.84/1.06      inference('eq_fact', [status(thm)], ['38'])).
% 0.84/1.06  thf('59', plain,
% 0.84/1.06      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.84/1.06         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.84/1.06          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 0.84/1.06          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.84/1.06      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.84/1.06  thf('60', plain,
% 0.84/1.06      ((((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))
% 0.84/1.06        | (r2_hidden @ 
% 0.84/1.06           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06           sk_C_1)
% 0.84/1.06        | ~ (r2_hidden @ 
% 0.84/1.06             (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06             k1_xboole_0)
% 0.84/1.06        | ((k1_xboole_0)
% 0.84/1.06            = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['58', '59'])).
% 0.84/1.06  thf('61', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.84/1.06      inference('clc', [status(thm)], ['35', '36'])).
% 0.84/1.06  thf('62', plain,
% 0.84/1.06      ((((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))
% 0.84/1.06        | (r2_hidden @ 
% 0.84/1.06           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06           sk_C_1)
% 0.84/1.06        | ~ (r2_hidden @ 
% 0.84/1.06             (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06             k1_xboole_0)
% 0.84/1.06        | ((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B)))),
% 0.84/1.06      inference('demod', [status(thm)], ['60', '61'])).
% 0.84/1.06  thf('63', plain,
% 0.84/1.06      ((~ (r2_hidden @ 
% 0.84/1.06           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06           k1_xboole_0)
% 0.84/1.06        | (r2_hidden @ 
% 0.84/1.06           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06           sk_C_1)
% 0.84/1.06        | ((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B)))),
% 0.84/1.06      inference('simplify', [status(thm)], ['62'])).
% 0.84/1.06  thf('64', plain,
% 0.84/1.06      ((((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))
% 0.84/1.06        | (r2_hidden @ 
% 0.84/1.06           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06           sk_C_1))),
% 0.84/1.06      inference('clc', [status(thm)], ['57', '63'])).
% 0.84/1.06  thf('65', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.06         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.84/1.06          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X1)
% 0.84/1.06          | ((X2) = (k2_xboole_0 @ X0 @ X1))
% 0.84/1.06          | ~ (r1_xboole_0 @ X0 @ X3)
% 0.84/1.06          | ~ (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X3))),
% 0.84/1.06      inference('sup-', [status(thm)], ['40', '41'])).
% 0.84/1.06  thf('66', plain,
% 0.84/1.06      ((((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))
% 0.84/1.06        | ~ (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.84/1.06        | ((k1_xboole_0)
% 0.84/1.06            = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0))
% 0.84/1.06        | (r2_hidden @ 
% 0.84/1.06           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06           k1_xboole_0)
% 0.84/1.06        | (r2_hidden @ 
% 0.84/1.06           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06           k1_xboole_0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['64', '65'])).
% 0.84/1.06  thf('67', plain,
% 0.84/1.06      (![X0 : $i]: (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)),
% 0.84/1.06      inference('demod', [status(thm)], ['52', '53'])).
% 0.84/1.06  thf('68', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.84/1.06      inference('clc', [status(thm)], ['35', '36'])).
% 0.84/1.06  thf('69', plain,
% 0.84/1.06      ((((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))
% 0.84/1.06        | ((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))
% 0.84/1.06        | (r2_hidden @ 
% 0.84/1.06           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06           k1_xboole_0)
% 0.84/1.06        | (r2_hidden @ 
% 0.84/1.06           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06           k1_xboole_0))),
% 0.84/1.06      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.84/1.06  thf('70', plain,
% 0.84/1.06      (((r2_hidden @ 
% 0.84/1.06         (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06         k1_xboole_0)
% 0.84/1.06        | ((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B)))),
% 0.84/1.06      inference('simplify', [status(thm)], ['69'])).
% 0.84/1.06  thf('71', plain,
% 0.84/1.06      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.84/1.06         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.84/1.06          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.84/1.06          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.84/1.06      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.84/1.06  thf('72', plain,
% 0.84/1.06      ((((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))
% 0.84/1.06        | ~ (r2_hidden @ 
% 0.84/1.06             (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06             k1_xboole_0)
% 0.84/1.06        | ((k1_xboole_0)
% 0.84/1.06            = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['70', '71'])).
% 0.84/1.06  thf('73', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.84/1.06      inference('clc', [status(thm)], ['35', '36'])).
% 0.84/1.06  thf('74', plain,
% 0.84/1.06      ((((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))
% 0.84/1.06        | ~ (r2_hidden @ 
% 0.84/1.06             (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06             k1_xboole_0)
% 0.84/1.06        | ((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B)))),
% 0.84/1.06      inference('demod', [status(thm)], ['72', '73'])).
% 0.84/1.06  thf('75', plain,
% 0.84/1.06      ((~ (r2_hidden @ 
% 0.84/1.06           (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06           k1_xboole_0)
% 0.84/1.06        | ((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B)))),
% 0.84/1.06      inference('simplify', [status(thm)], ['74'])).
% 0.84/1.06  thf('76', plain,
% 0.84/1.06      (((r2_hidden @ 
% 0.84/1.06         (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06         k1_xboole_0)
% 0.84/1.06        | ((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B)))),
% 0.84/1.06      inference('simplify', [status(thm)], ['69'])).
% 0.84/1.06  thf('77', plain,
% 0.84/1.06      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.84/1.06         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.84/1.06      inference('simplify', [status(thm)], ['46'])).
% 0.84/1.06  thf('78', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))
% 0.84/1.06          | (r2_hidden @ 
% 0.84/1.06             (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06             (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['76', '77'])).
% 0.84/1.06  thf('79', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.84/1.06      inference('clc', [status(thm)], ['35', '36'])).
% 0.84/1.06  thf('80', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))
% 0.84/1.06          | (r2_hidden @ 
% 0.84/1.06             (sk_D @ k1_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.84/1.06             X0))),
% 0.84/1.06      inference('demod', [status(thm)], ['78', '79'])).
% 0.84/1.06  thf('81', plain, (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))),
% 0.84/1.06      inference('clc', [status(thm)], ['75', '80'])).
% 0.84/1.06  thf(t38_zfmisc_1, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.84/1.06       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.84/1.06  thf('82', plain,
% 0.84/1.06      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.84/1.06         ((r2_hidden @ X21 @ X22)
% 0.84/1.06          | ~ (r1_tarski @ (k2_tarski @ X21 @ X23) @ X22))),
% 0.84/1.06      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.84/1.06  thf('83', plain,
% 0.84/1.06      (![X0 : $i]: (~ (r1_tarski @ k1_xboole_0 @ X0) | (r2_hidden @ sk_A @ X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['81', '82'])).
% 0.84/1.06  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.84/1.06  thf('84', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.84/1.06      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.84/1.06  thf('85', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 0.84/1.06      inference('demod', [status(thm)], ['83', '84'])).
% 0.84/1.06  thf('86', plain,
% 0.84/1.06      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X10 @ X8)
% 0.84/1.06          | ~ (r2_hidden @ X10 @ X11)
% 0.84/1.06          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.84/1.06      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.84/1.06  thf('87', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         (~ (r1_xboole_0 @ X0 @ X1) | ~ (r2_hidden @ sk_A @ X1))),
% 0.84/1.06      inference('sup-', [status(thm)], ['85', '86'])).
% 0.84/1.06  thf('88', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 0.84/1.06      inference('demod', [status(thm)], ['83', '84'])).
% 0.84/1.06  thf('89', plain, (![X0 : $i, X1 : $i]: ~ (r1_xboole_0 @ X0 @ X1)),
% 0.84/1.06      inference('demod', [status(thm)], ['87', '88'])).
% 0.84/1.06  thf('90', plain, ($false), inference('sup-', [status(thm)], ['0', '89'])).
% 0.84/1.06  
% 0.84/1.06  % SZS output end Refutation
% 0.84/1.06  
% 0.84/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

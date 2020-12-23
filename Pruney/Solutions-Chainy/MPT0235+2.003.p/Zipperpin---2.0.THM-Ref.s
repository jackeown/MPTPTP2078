%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4GLkBKsHxD

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:58 EST 2020

% Result     : Theorem 5.69s
% Output     : Refutation 5.69s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 138 expanded)
%              Number of leaves         :   15 (  40 expanded)
%              Depth                    :   24
%              Number of atoms          :  849 (2240 expanded)
%              Number of equality atoms :   99 ( 299 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t30_zfmisc_1,conjecture,(
    ! [A: $i] :
      ( ( k1_zfmisc_1 @ ( k1_tarski @ A ) )
      = ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_zfmisc_1 @ ( k1_tarski @ A ) )
        = ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_zfmisc_1])).

thf('0',plain,(
    ( k1_zfmisc_1 @ ( k1_tarski @ sk_A ) )
 != ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14
        = ( k1_zfmisc_1 @ X11 ) )
      | ( r1_tarski @ ( sk_C_1 @ X14 @ X11 ) @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X11 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X17
        = ( k2_tarski @ X15 @ X16 ) )
      | ( X17
        = ( k1_tarski @ X16 ) )
      | ( X17
        = ( k1_tarski @ X15 ) )
      | ( X17 = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ ( k2_tarski @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( X1
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ( X7 = X6 )
      | ( X7 = X3 )
      | ( X5
       != ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('10',plain,(
    ! [X3: $i,X6: $i,X7: $i] :
      ( ( X7 = X3 )
      | ( X7 = X6 )
      | ~ ( r2_hidden @ X7 @ ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C_1 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C_1 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X2 ) ) )
      | ( ( sk_C_1 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
        = X1 )
      | ( ( sk_C_1 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_C_1 @ ( k2_tarski @ X0 @ X2 ) @ ( k1_tarski @ X1 ) )
        = X2 )
      | ( ( k2_tarski @ X0 @ X2 )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X1 ) ) )
      | ( ( sk_C_1 @ ( k2_tarski @ X0 @ X2 ) @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 )
      | ( ( sk_C_1 @ ( k2_tarski @ X0 @ X2 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['11'])).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ X2 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ X2 ) @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ X2 )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X1 ) ) )
      | ( ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ X2 ) @ ( k1_tarski @ X1 ) )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != X1 )
      | ( ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ X1 ) @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( ( k2_tarski @ k1_xboole_0 @ X1 )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ X1 ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('17',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14
        = ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ ( sk_C_1 @ X14 @ X11 ) @ X11 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X14 @ X11 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k1_tarski @ X19 ) @ ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_tarski @ X0 ) @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','23'])).

thf('25',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('26',plain,(
    ! [X3: $i,X6: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X6 @ X3 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('30',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14
        = ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ ( sk_C_1 @ X14 @ X11 ) @ X11 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X14 @ X11 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('32',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4 != X6 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('37',plain,(
    ! [X3: $i,X6: $i] :
      ( r2_hidden @ X6 @ ( k2_tarski @ X6 @ X3 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ( k1_zfmisc_1 @ ( k1_tarski @ sk_A ) )
 != ( k1_zfmisc_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4GLkBKsHxD
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:35:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.69/5.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.69/5.89  % Solved by: fo/fo7.sh
% 5.69/5.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.69/5.89  % done 4271 iterations in 5.427s
% 5.69/5.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.69/5.89  % SZS output start Refutation
% 5.69/5.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.69/5.89  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.69/5.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.69/5.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.69/5.89  thf(sk_A_type, type, sk_A: $i).
% 5.69/5.89  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 5.69/5.89  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.69/5.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.69/5.89  thf(t30_zfmisc_1, conjecture,
% 5.69/5.89    (![A:$i]:
% 5.69/5.89     ( ( k1_zfmisc_1 @ ( k1_tarski @ A ) ) =
% 5.69/5.89       ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 5.69/5.89  thf(zf_stmt_0, negated_conjecture,
% 5.69/5.89    (~( ![A:$i]:
% 5.69/5.89        ( ( k1_zfmisc_1 @ ( k1_tarski @ A ) ) =
% 5.69/5.89          ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ A ) ) ) )),
% 5.69/5.89    inference('cnf.neg', [status(esa)], [t30_zfmisc_1])).
% 5.69/5.89  thf('0', plain,
% 5.69/5.89      (((k1_zfmisc_1 @ (k1_tarski @ sk_A))
% 5.69/5.89         != (k2_tarski @ k1_xboole_0 @ (k1_tarski @ sk_A)))),
% 5.69/5.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.69/5.89  thf(d1_zfmisc_1, axiom,
% 5.69/5.89    (![A:$i,B:$i]:
% 5.69/5.89     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 5.69/5.89       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 5.69/5.89  thf('1', plain,
% 5.69/5.89      (![X11 : $i, X14 : $i]:
% 5.69/5.89         (((X14) = (k1_zfmisc_1 @ X11))
% 5.69/5.89          | (r1_tarski @ (sk_C_1 @ X14 @ X11) @ X11)
% 5.69/5.89          | (r2_hidden @ (sk_C_1 @ X14 @ X11) @ X14))),
% 5.69/5.89      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 5.69/5.89  thf(t69_enumset1, axiom,
% 5.69/5.89    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 5.69/5.89  thf('2', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 5.69/5.89      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.69/5.89  thf(l45_zfmisc_1, axiom,
% 5.69/5.89    (![A:$i,B:$i,C:$i]:
% 5.69/5.89     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 5.69/5.89       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 5.69/5.89            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 5.69/5.89  thf('3', plain,
% 5.69/5.89      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.69/5.89         (((X17) = (k2_tarski @ X15 @ X16))
% 5.69/5.89          | ((X17) = (k1_tarski @ X16))
% 5.69/5.89          | ((X17) = (k1_tarski @ X15))
% 5.69/5.89          | ((X17) = (k1_xboole_0))
% 5.69/5.89          | ~ (r1_tarski @ X17 @ (k2_tarski @ X15 @ X16)))),
% 5.69/5.89      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 5.69/5.89  thf('4', plain,
% 5.69/5.89      (![X0 : $i, X1 : $i]:
% 5.69/5.89         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 5.69/5.89          | ((X1) = (k1_xboole_0))
% 5.69/5.89          | ((X1) = (k1_tarski @ X0))
% 5.69/5.89          | ((X1) = (k1_tarski @ X0))
% 5.69/5.89          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 5.69/5.89      inference('sup-', [status(thm)], ['2', '3'])).
% 5.69/5.89  thf('5', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 5.69/5.89      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.69/5.89  thf('6', plain,
% 5.69/5.89      (![X0 : $i, X1 : $i]:
% 5.69/5.89         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 5.69/5.89          | ((X1) = (k1_xboole_0))
% 5.69/5.89          | ((X1) = (k1_tarski @ X0))
% 5.69/5.89          | ((X1) = (k1_tarski @ X0))
% 5.69/5.89          | ((X1) = (k1_tarski @ X0)))),
% 5.69/5.89      inference('demod', [status(thm)], ['4', '5'])).
% 5.69/5.89  thf('7', plain,
% 5.69/5.89      (![X0 : $i, X1 : $i]:
% 5.69/5.89         (((X1) = (k1_tarski @ X0))
% 5.69/5.89          | ((X1) = (k1_xboole_0))
% 5.69/5.89          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 5.69/5.89      inference('simplify', [status(thm)], ['6'])).
% 5.69/5.89  thf('8', plain,
% 5.69/5.89      (![X0 : $i, X1 : $i]:
% 5.69/5.89         ((r2_hidden @ (sk_C_1 @ X1 @ (k1_tarski @ X0)) @ X1)
% 5.69/5.89          | ((X1) = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 5.69/5.89          | ((sk_C_1 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0))
% 5.69/5.89          | ((sk_C_1 @ X1 @ (k1_tarski @ X0)) = (k1_tarski @ X0)))),
% 5.69/5.89      inference('sup-', [status(thm)], ['1', '7'])).
% 5.69/5.89  thf(d2_tarski, axiom,
% 5.69/5.89    (![A:$i,B:$i,C:$i]:
% 5.69/5.89     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 5.69/5.89       ( ![D:$i]:
% 5.69/5.89         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 5.69/5.89  thf('9', plain,
% 5.69/5.89      (![X3 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 5.69/5.89         (~ (r2_hidden @ X7 @ X5)
% 5.69/5.89          | ((X7) = (X6))
% 5.69/5.89          | ((X7) = (X3))
% 5.69/5.89          | ((X5) != (k2_tarski @ X6 @ X3)))),
% 5.69/5.89      inference('cnf', [status(esa)], [d2_tarski])).
% 5.69/5.89  thf('10', plain,
% 5.69/5.89      (![X3 : $i, X6 : $i, X7 : $i]:
% 5.69/5.89         (((X7) = (X3))
% 5.69/5.89          | ((X7) = (X6))
% 5.69/5.89          | ~ (r2_hidden @ X7 @ (k2_tarski @ X6 @ X3)))),
% 5.69/5.89      inference('simplify', [status(thm)], ['9'])).
% 5.69/5.89  thf('11', plain,
% 5.69/5.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.69/5.89         (((sk_C_1 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 5.69/5.89            = (k1_tarski @ X2))
% 5.69/5.89          | ((sk_C_1 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 5.69/5.89              = (k1_xboole_0))
% 5.69/5.89          | ((k2_tarski @ X1 @ X0) = (k1_zfmisc_1 @ (k1_tarski @ X2)))
% 5.69/5.89          | ((sk_C_1 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)) = (X1))
% 5.69/5.89          | ((sk_C_1 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)) = (X0)))),
% 5.69/5.89      inference('sup-', [status(thm)], ['8', '10'])).
% 5.69/5.89  thf('12', plain,
% 5.69/5.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.69/5.89         (((X0) != (k1_xboole_0))
% 5.69/5.89          | ((sk_C_1 @ (k2_tarski @ X0 @ X2) @ (k1_tarski @ X1)) = (X2))
% 5.69/5.89          | ((k2_tarski @ X0 @ X2) = (k1_zfmisc_1 @ (k1_tarski @ X1)))
% 5.69/5.89          | ((sk_C_1 @ (k2_tarski @ X0 @ X2) @ (k1_tarski @ X1))
% 5.69/5.89              = (k1_xboole_0))
% 5.69/5.89          | ((sk_C_1 @ (k2_tarski @ X0 @ X2) @ (k1_tarski @ X1))
% 5.69/5.89              = (k1_tarski @ X1)))),
% 5.69/5.89      inference('eq_fact', [status(thm)], ['11'])).
% 5.69/5.89  thf('13', plain,
% 5.69/5.89      (![X1 : $i, X2 : $i]:
% 5.69/5.89         (((sk_C_1 @ (k2_tarski @ k1_xboole_0 @ X2) @ (k1_tarski @ X1))
% 5.69/5.89            = (k1_tarski @ X1))
% 5.69/5.89          | ((sk_C_1 @ (k2_tarski @ k1_xboole_0 @ X2) @ (k1_tarski @ X1))
% 5.69/5.89              = (k1_xboole_0))
% 5.69/5.89          | ((k2_tarski @ k1_xboole_0 @ X2) = (k1_zfmisc_1 @ (k1_tarski @ X1)))
% 5.69/5.89          | ((sk_C_1 @ (k2_tarski @ k1_xboole_0 @ X2) @ (k1_tarski @ X1))
% 5.69/5.89              = (X2)))),
% 5.69/5.89      inference('simplify', [status(thm)], ['12'])).
% 5.69/5.89  thf('14', plain,
% 5.69/5.89      (![X0 : $i, X1 : $i]:
% 5.69/5.89         (((k1_tarski @ X0) != (X1))
% 5.69/5.89          | ((sk_C_1 @ (k2_tarski @ k1_xboole_0 @ X1) @ (k1_tarski @ X0))
% 5.69/5.89              = (X1))
% 5.69/5.89          | ((k2_tarski @ k1_xboole_0 @ X1) = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 5.69/5.89          | ((sk_C_1 @ (k2_tarski @ k1_xboole_0 @ X1) @ (k1_tarski @ X0))
% 5.69/5.89              = (k1_xboole_0)))),
% 5.69/5.89      inference('eq_fact', [status(thm)], ['13'])).
% 5.69/5.89  thf('15', plain,
% 5.69/5.89      (![X0 : $i]:
% 5.69/5.89         (((sk_C_1 @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 5.69/5.89            (k1_tarski @ X0)) = (k1_xboole_0))
% 5.69/5.89          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89              = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 5.69/5.89          | ((sk_C_1 @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 5.69/5.89              (k1_tarski @ X0)) = (k1_tarski @ X0)))),
% 5.69/5.89      inference('simplify', [status(thm)], ['14'])).
% 5.69/5.89  thf('16', plain,
% 5.69/5.89      (![X0 : $i]:
% 5.69/5.89         (((sk_C_1 @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 5.69/5.89            (k1_tarski @ X0)) = (k1_xboole_0))
% 5.69/5.89          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89              = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 5.69/5.89          | ((sk_C_1 @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 5.69/5.89              (k1_tarski @ X0)) = (k1_tarski @ X0)))),
% 5.69/5.89      inference('simplify', [status(thm)], ['14'])).
% 5.69/5.89  thf('17', plain,
% 5.69/5.89      (![X11 : $i, X14 : $i]:
% 5.69/5.89         (((X14) = (k1_zfmisc_1 @ X11))
% 5.69/5.89          | ~ (r1_tarski @ (sk_C_1 @ X14 @ X11) @ X11)
% 5.69/5.89          | ~ (r2_hidden @ (sk_C_1 @ X14 @ X11) @ X14))),
% 5.69/5.89      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 5.69/5.89  thf('18', plain,
% 5.69/5.89      (![X0 : $i]:
% 5.69/5.89         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 5.69/5.89          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89              = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 5.69/5.89          | ((sk_C_1 @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 5.69/5.89              (k1_tarski @ X0)) = (k1_xboole_0))
% 5.69/5.89          | ~ (r2_hidden @ 
% 5.69/5.89               (sk_C_1 @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 5.69/5.89                (k1_tarski @ X0)) @ 
% 5.69/5.89               (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)))
% 5.69/5.89          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89              = (k1_zfmisc_1 @ (k1_tarski @ X0))))),
% 5.69/5.89      inference('sup-', [status(thm)], ['16', '17'])).
% 5.69/5.89  thf('19', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 5.69/5.89      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.69/5.89  thf(t12_zfmisc_1, axiom,
% 5.69/5.89    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 5.69/5.89  thf('20', plain,
% 5.69/5.89      (![X19 : $i, X20 : $i]:
% 5.69/5.89         (r1_tarski @ (k1_tarski @ X19) @ (k2_tarski @ X19 @ X20))),
% 5.69/5.89      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 5.69/5.89  thf('21', plain,
% 5.69/5.89      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 5.69/5.89      inference('sup+', [status(thm)], ['19', '20'])).
% 5.69/5.89  thf('22', plain,
% 5.69/5.89      (![X0 : $i]:
% 5.69/5.89         (((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89            = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 5.69/5.89          | ((sk_C_1 @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 5.69/5.89              (k1_tarski @ X0)) = (k1_xboole_0))
% 5.69/5.89          | ~ (r2_hidden @ 
% 5.69/5.89               (sk_C_1 @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 5.69/5.89                (k1_tarski @ X0)) @ 
% 5.69/5.89               (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)))
% 5.69/5.89          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89              = (k1_zfmisc_1 @ (k1_tarski @ X0))))),
% 5.69/5.89      inference('demod', [status(thm)], ['18', '21'])).
% 5.69/5.89  thf('23', plain,
% 5.69/5.89      (![X0 : $i]:
% 5.69/5.89         (~ (r2_hidden @ 
% 5.69/5.89             (sk_C_1 @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 5.69/5.89              (k1_tarski @ X0)) @ 
% 5.69/5.89             (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)))
% 5.69/5.89          | ((sk_C_1 @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 5.69/5.89              (k1_tarski @ X0)) = (k1_xboole_0))
% 5.69/5.89          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89              = (k1_zfmisc_1 @ (k1_tarski @ X0))))),
% 5.69/5.89      inference('simplify', [status(thm)], ['22'])).
% 5.69/5.89  thf('24', plain,
% 5.69/5.89      (![X0 : $i]:
% 5.69/5.89         (~ (r2_hidden @ (k1_tarski @ X0) @ 
% 5.69/5.89             (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)))
% 5.69/5.89          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89              = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 5.69/5.89          | ((sk_C_1 @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 5.69/5.89              (k1_tarski @ X0)) = (k1_xboole_0))
% 5.69/5.89          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89              = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 5.69/5.89          | ((sk_C_1 @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 5.69/5.89              (k1_tarski @ X0)) = (k1_xboole_0)))),
% 5.69/5.89      inference('sup-', [status(thm)], ['15', '23'])).
% 5.69/5.89  thf('25', plain,
% 5.69/5.89      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 5.69/5.89         (((X4) != (X3))
% 5.69/5.89          | (r2_hidden @ X4 @ X5)
% 5.69/5.89          | ((X5) != (k2_tarski @ X6 @ X3)))),
% 5.69/5.89      inference('cnf', [status(esa)], [d2_tarski])).
% 5.69/5.89  thf('26', plain,
% 5.69/5.89      (![X3 : $i, X6 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X6 @ X3))),
% 5.69/5.89      inference('simplify', [status(thm)], ['25'])).
% 5.69/5.89  thf('27', plain,
% 5.69/5.89      (![X0 : $i]:
% 5.69/5.89         (((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89            = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 5.69/5.89          | ((sk_C_1 @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 5.69/5.89              (k1_tarski @ X0)) = (k1_xboole_0))
% 5.69/5.89          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89              = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 5.69/5.89          | ((sk_C_1 @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 5.69/5.89              (k1_tarski @ X0)) = (k1_xboole_0)))),
% 5.69/5.89      inference('demod', [status(thm)], ['24', '26'])).
% 5.69/5.89  thf('28', plain,
% 5.69/5.89      (![X0 : $i]:
% 5.69/5.89         (((sk_C_1 @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 5.69/5.89            (k1_tarski @ X0)) = (k1_xboole_0))
% 5.69/5.89          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89              = (k1_zfmisc_1 @ (k1_tarski @ X0))))),
% 5.69/5.89      inference('simplify', [status(thm)], ['27'])).
% 5.69/5.89  thf('29', plain,
% 5.69/5.89      (![X0 : $i]:
% 5.69/5.89         (((sk_C_1 @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 5.69/5.89            (k1_tarski @ X0)) = (k1_xboole_0))
% 5.69/5.89          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89              = (k1_zfmisc_1 @ (k1_tarski @ X0))))),
% 5.69/5.89      inference('simplify', [status(thm)], ['27'])).
% 5.69/5.89  thf('30', plain,
% 5.69/5.89      (![X11 : $i, X14 : $i]:
% 5.69/5.89         (((X14) = (k1_zfmisc_1 @ X11))
% 5.69/5.89          | ~ (r1_tarski @ (sk_C_1 @ X14 @ X11) @ X11)
% 5.69/5.89          | ~ (r2_hidden @ (sk_C_1 @ X14 @ X11) @ X14))),
% 5.69/5.89      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 5.69/5.89  thf('31', plain,
% 5.69/5.89      (![X0 : $i]:
% 5.69/5.89         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89              = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 5.69/5.89          | ~ (r2_hidden @ 
% 5.69/5.89               (sk_C_1 @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 5.69/5.89                (k1_tarski @ X0)) @ 
% 5.69/5.89               (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)))
% 5.69/5.89          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89              = (k1_zfmisc_1 @ (k1_tarski @ X0))))),
% 5.69/5.89      inference('sup-', [status(thm)], ['29', '30'])).
% 5.69/5.89  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.69/5.89  thf('32', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 5.69/5.89      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.69/5.89  thf('33', plain,
% 5.69/5.89      (![X0 : $i]:
% 5.69/5.89         (((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89            = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 5.69/5.89          | ~ (r2_hidden @ 
% 5.69/5.89               (sk_C_1 @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 5.69/5.89                (k1_tarski @ X0)) @ 
% 5.69/5.89               (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)))
% 5.69/5.89          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89              = (k1_zfmisc_1 @ (k1_tarski @ X0))))),
% 5.69/5.89      inference('demod', [status(thm)], ['31', '32'])).
% 5.69/5.89  thf('34', plain,
% 5.69/5.89      (![X0 : $i]:
% 5.69/5.89         (~ (r2_hidden @ 
% 5.69/5.89             (sk_C_1 @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 5.69/5.89              (k1_tarski @ X0)) @ 
% 5.69/5.89             (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)))
% 5.69/5.89          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89              = (k1_zfmisc_1 @ (k1_tarski @ X0))))),
% 5.69/5.89      inference('simplify', [status(thm)], ['33'])).
% 5.69/5.89  thf('35', plain,
% 5.69/5.89      (![X0 : $i]:
% 5.69/5.89         (~ (r2_hidden @ k1_xboole_0 @ 
% 5.69/5.89             (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)))
% 5.69/5.89          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89              = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 5.69/5.89          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89              = (k1_zfmisc_1 @ (k1_tarski @ X0))))),
% 5.69/5.89      inference('sup-', [status(thm)], ['28', '34'])).
% 5.69/5.89  thf('36', plain,
% 5.69/5.89      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 5.69/5.89         (((X4) != (X6))
% 5.69/5.89          | (r2_hidden @ X4 @ X5)
% 5.69/5.89          | ((X5) != (k2_tarski @ X6 @ X3)))),
% 5.69/5.89      inference('cnf', [status(esa)], [d2_tarski])).
% 5.69/5.89  thf('37', plain,
% 5.69/5.89      (![X3 : $i, X6 : $i]: (r2_hidden @ X6 @ (k2_tarski @ X6 @ X3))),
% 5.69/5.89      inference('simplify', [status(thm)], ['36'])).
% 5.69/5.89  thf('38', plain,
% 5.69/5.89      (![X0 : $i]:
% 5.69/5.89         (((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89            = (k1_zfmisc_1 @ (k1_tarski @ X0)))
% 5.69/5.89          | ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89              = (k1_zfmisc_1 @ (k1_tarski @ X0))))),
% 5.69/5.89      inference('demod', [status(thm)], ['35', '37'])).
% 5.69/5.89  thf('39', plain,
% 5.69/5.89      (![X0 : $i]:
% 5.69/5.89         ((k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.69/5.89           = (k1_zfmisc_1 @ (k1_tarski @ X0)))),
% 5.69/5.89      inference('simplify', [status(thm)], ['38'])).
% 5.69/5.89  thf('40', plain,
% 5.69/5.89      (((k1_zfmisc_1 @ (k1_tarski @ sk_A))
% 5.69/5.89         != (k1_zfmisc_1 @ (k1_tarski @ sk_A)))),
% 5.69/5.89      inference('demod', [status(thm)], ['0', '39'])).
% 5.69/5.89  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 5.69/5.89  
% 5.69/5.89  % SZS output end Refutation
% 5.69/5.89  
% 5.73/5.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

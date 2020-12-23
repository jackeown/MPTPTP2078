%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0235+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2OlfuuEvVJ

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:33 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 107 expanded)
%              Number of leaves         :   12 (  30 expanded)
%              Depth                    :   21
%              Number of atoms          :  756 (1870 expanded)
%              Number of equality atoms :   83 ( 232 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X1: $i,X4: $i] :
      ( ( X4
        = ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ ( sk_C @ X4 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X4 @ X1 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12
        = ( k1_tarski @ X11 ) )
      | ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( X1
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ( X9 = X8 )
      | ( X9 = X5 )
      | ( X7
       != ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('5',plain,(
    ! [X5: $i,X8: $i,X9: $i] :
      ( ( X9 = X5 )
      | ( X9 = X8 )
      | ~ ( r2_hidden @ X9 @ ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X2 ) ) )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
        = X1 )
      | ( ( sk_C @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X2 ) @ ( k1_tarski @ X1 ) )
        = X2 )
      | ( ( k2_tarski @ X0 @ X2 )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X1 ) ) )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X2 ) @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 )
      | ( ( sk_C @ ( k2_tarski @ X0 @ X2 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['6'])).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ X2 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ X2 ) @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ X2 )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X1 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ X2 ) @ ( k1_tarski @ X1 ) )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != X1 )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ X1 ) @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( ( k2_tarski @ k1_xboole_0 @ X1 )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ X1 ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('12',plain,(
    ! [X1: $i,X4: $i] :
      ( ( X4
        = ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r1_tarski @ ( sk_C @ X4 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X4 @ X1 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ ( k1_tarski @ X13 ) )
      | ( X12
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('15',plain,(
    ! [X13: $i] :
      ( r1_tarski @ ( k1_tarski @ X13 ) @ ( k1_tarski @ X13 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_tarski @ X0 ) @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X5 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('20',plain,(
    ! [X5: $i,X8: $i] :
      ( r2_hidden @ X5 @ ( k2_tarski @ X8 @ X5 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('24',plain,(
    ! [X1: $i,X4: $i] :
      ( ( X4
        = ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r1_tarski @ ( sk_C @ X4 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X4 @ X1 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ ( k1_tarski @ X13 ) )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('27',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X13 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X8 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('32',plain,(
    ! [X5: $i,X8: $i] :
      ( r2_hidden @ X8 @ ( k2_tarski @ X8 @ X5 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = ( k1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ( k1_zfmisc_1 @ ( k1_tarski @ sk_A ) )
 != ( k1_zfmisc_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','34'])).

thf('36',plain,(
    $false ),
    inference(simplify,[status(thm)],['35'])).


%------------------------------------------------------------------------------

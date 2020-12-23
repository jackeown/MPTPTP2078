%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0212+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xHtHivqIN8

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:49 EST 2020

% Result     : Theorem 16.22s
% Output     : Refutation 16.22s
% Verified   : 
% Statistics : Number of formulae       :   53 (  62 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  305 ( 364 expanded)
%              Number of equality atoms :   29 (  36 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X436: $i,X437: $i,X438: $i] :
      ( ( X437 != X436 )
      | ( r2_hidden @ ( X437 @ X438 ) )
      | ( X438
       != ( k1_tarski @ X436 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X436: $i] :
      ( r2_hidden @ ( X436 @ ( k1_tarski @ X436 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ A ) )
         => ( r2_hidden @ ( C @ B ) ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ ( X14 @ X16 ) )
      | ( r2_hidden @ ( sk_C @ ( X16 @ X14 ) @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ( r1_tarski @ ( C @ A ) ) ) ) )).

thf('3',plain,(
    ! [X961: $i,X962: $i,X963: $i] :
      ( ~ ( r2_hidden @ ( X963 @ X962 ) )
      | ( r1_tarski @ ( X963 @ X961 ) )
      | ( X962
       != ( k1_zfmisc_1 @ X961 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('4',plain,(
    ! [X961: $i,X963: $i] :
      ( ( r1_tarski @ ( X963 @ X961 ) )
      | ~ ( r2_hidden @ ( X963 @ ( k1_zfmisc_1 @ X961 ) ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( sk_C @ ( X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ ( A @ k1_xboole_0 ) )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X245: $i] :
      ( ( X245 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X245 @ k1_xboole_0 ) ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,(
    ! [X245: $i] :
      ( ( X245 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X245 @ o_0_0_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ o_0_0_xboole_0 @ X0 ) )
      | ( ( sk_C @ ( X0 @ ( k1_zfmisc_1 @ o_0_0_xboole_0 ) ) )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ ( X14 @ X16 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( X16 @ X14 ) @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( o_0_0_xboole_0 @ X0 ) )
      | ( r1_tarski @ ( k1_zfmisc_1 @ o_0_0_xboole_0 @ X0 ) )
      | ( r1_tarski @ ( k1_zfmisc_1 @ o_0_0_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ o_0_0_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ ( o_0_0_xboole_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    r1_tarski @ ( k1_zfmisc_1 @ o_0_0_xboole_0 @ ( k1_tarski @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X78: $i,X80: $i] :
      ( ( X78 = X80 )
      | ~ ( r1_tarski @ ( X80 @ X78 ) )
      | ~ ( r1_tarski @ ( X78 @ X80 ) ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ o_0_0_xboole_0 @ ( k1_zfmisc_1 @ o_0_0_xboole_0 ) ) )
    | ( ( k1_tarski @ o_0_0_xboole_0 )
      = ( k1_zfmisc_1 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ A ) ) )).

thf('17',plain,(
    ! [X216: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ X216 ) ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('18',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('19',plain,(
    ! [X216: $i] :
      ( r1_tarski @ ( o_0_0_xboole_0 @ X216 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X960: $i,X961: $i,X962: $i] :
      ( ~ ( r1_tarski @ ( X960 @ X961 ) )
      | ( r2_hidden @ ( X960 @ X962 ) )
      | ( X962
       != ( k1_zfmisc_1 @ X961 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('21',plain,(
    ! [X960: $i,X961: $i] :
      ( ( r2_hidden @ ( X960 @ ( k1_zfmisc_1 @ X961 ) ) )
      | ~ ( r1_tarski @ ( X960 @ X961 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ ( X14 @ X16 ) )
      | ( r2_hidden @ ( sk_C @ ( X16 @ X14 ) @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X436: $i,X438: $i,X439: $i] :
      ( ~ ( r2_hidden @ ( X439 @ X438 ) )
      | ( X439 = X436 )
      | ( X438
       != ( k1_tarski @ X436 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('25',plain,(
    ! [X436: $i,X439: $i] :
      ( ( X439 = X436 )
      | ~ ( r2_hidden @ ( X439 @ ( k1_tarski @ X436 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 @ X1 ) )
      | ( ( sk_C @ ( X1 @ ( k1_tarski @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ ( X14 @ X16 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( X16 @ X14 ) @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( X0 @ X1 ) )
      | ( r1_tarski @ ( k1_tarski @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,
    ( ( k1_tarski @ o_0_0_xboole_0 )
    = ( k1_zfmisc_1 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['16','30'])).

thf(t1_zfmisc_1,conjecture,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t1_zfmisc_1])).

thf('32',plain,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('34',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('35',plain,(
    ( k1_zfmisc_1 @ o_0_0_xboole_0 )
 != ( k1_tarski @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','35'])).

%------------------------------------------------------------------------------

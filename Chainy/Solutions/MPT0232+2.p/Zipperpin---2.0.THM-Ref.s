%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0232+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kc1oznIsaR

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  33 expanded)
%              Number of leaves         :   10 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  127 ( 223 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_8_type,type,(
    sk_C_8: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t27_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ ( A @ B ) @ ( k1_tarski @ C ) ) )
     => ( ( k2_tarski @ ( A @ B ) )
        = ( k1_tarski @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ ( A @ B ) @ ( k1_tarski @ C ) ) )
       => ( ( k2_tarski @ ( A @ B ) )
          = ( k1_tarski @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ ( k1_tarski @ sk_C_8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ ( k1_tarski @ sk_C_8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ ( A @ B ) @ ( k1_tarski @ C ) ) )
     => ( A = C ) ) )).

thf('2',plain,(
    ! [X1032: $i,X1033: $i,X1034: $i] :
      ( ( X1033 = X1032 )
      | ~ ( r1_tarski @ ( k2_tarski @ ( X1033 @ X1034 ) @ ( k1_tarski @ X1032 ) ) ) ) ),
    inference(cnf,[status(esa)],[t26_zfmisc_1])).

thf('3',plain,(
    sk_A_2 = sk_C_8 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ ( k1_tarski @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X78: $i,X80: $i] :
      ( ( X78 = X80 )
      | ~ ( r1_tarski @ ( X80 @ X78 ) )
      | ~ ( r1_tarski @ ( X78 @ X80 ) ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A_2 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) )
    | ( ( k1_tarski @ sk_A_2 )
      = ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A @ ( k2_tarski @ ( A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X1004: $i,X1005: $i] :
      ( r1_tarski @ ( k1_tarski @ X1004 @ ( k2_tarski @ ( X1004 @ X1005 ) ) ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('8',plain,
    ( ( k1_tarski @ sk_A_2 )
    = ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) )
 != ( k1_tarski @ sk_C_8 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_A_2 = sk_C_8 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('11',plain,(
    ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) )
 != ( k1_tarski @ sk_A_2 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

%------------------------------------------------------------------------------

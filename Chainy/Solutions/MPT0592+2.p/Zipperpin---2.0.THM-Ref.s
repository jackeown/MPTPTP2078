%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0592+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.41iJQpFfXh

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:57 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   33 (  50 expanded)
%              Number of leaves         :   10 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  146 ( 309 expanded)
%              Number of equality atoms :   36 (  72 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_15_type,type,(
    sk_B_15: $i )).

thf(sk_A_5_type,type,(
    sk_A_5: $i )).

thf(t196_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( ( ( k1_relat_1 @ A )
                = k1_xboole_0 )
              & ( ( k1_relat_1 @ B )
                = k1_xboole_0 ) )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( ( ( k1_relat_1 @ A )
                  = k1_xboole_0 )
                & ( ( k1_relat_1 @ B )
                  = k1_xboole_0 ) )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t196_relat_1])).

thf('0',plain,
    ( ( k1_relat_1 @ sk_B_15 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,
    ( ( k1_relat_1 @ sk_B_15 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X2475: $i] :
      ( ( ( k1_relat_1 @ X2475 )
       != k1_xboole_0 )
      | ( X2475 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2475 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    ! [X2475: $i] :
      ( ( ( k1_relat_1 @ X2475 )
       != o_0_0_xboole_0 )
      | ( X2475 = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X2475 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_15 )
    | ( sk_B_15 = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B_15 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( sk_B_15 = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    sk_B_15 = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    sk_A_5 != sk_B_15 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k1_relat_1 @ sk_A_5 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('14',plain,
    ( ( k1_relat_1 @ sk_A_5 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2475: $i] :
      ( ( ( k1_relat_1 @ X2475 )
       != o_0_0_xboole_0 )
      | ( X2475 = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X2475 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('16',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A_5 )
    | ( sk_A_5 = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_A_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( sk_A_5 = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    sk_A_5 = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    o_0_0_xboole_0 != sk_B_15 ),
    inference(demod,[status(thm)],['11','19'])).

thf('21',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['10','20'])).

%------------------------------------------------------------------------------

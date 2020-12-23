%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0468+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YU5WdWXhje

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:55 EST 2020

% Result     : Theorem 6.83s
% Output     : Refutation 6.83s
% Verified   : 
% Statistics : Number of formulae       :   28 (  34 expanded)
%              Number of leaves         :   13 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :  104 ( 150 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_27_type,type,(
    sk_C_27: $i > $i > $i )).

thf(sk_A_5_type,type,(
    sk_A_5: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_35_type,type,(
    sk_D_35: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ ( A @ B ) )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ ( C @ D ) @ A ) )
             => ( r2_hidden @ ( k4_tarski @ ( C @ D ) @ B ) ) ) ) ) )).

thf('0',plain,(
    ! [X2051: $i,X2052: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_27 @ ( X2051 @ X2052 ) @ ( sk_D_35 @ ( X2051 @ X2052 ) ) ) @ X2052 ) )
      | ( r1_tarski @ ( X2052 @ X2051 ) )
      | ~ ( v1_relat_1 @ X2052 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t56_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ ( B @ C ) @ A ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ! [B: $i,C: $i] :
              ~ ( r2_hidden @ ( k4_tarski @ ( B @ C ) @ A ) )
         => ( A = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_relat_1])).

thf('1',plain,(
    ! [X2185: $i,X2186: $i] :
      ~ ( r2_hidden @ ( k4_tarski @ ( X2185 @ X2186 ) @ sk_A_5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A_5 )
      | ( r1_tarski @ ( sk_A_5 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_A_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_A_5 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ ( A @ k1_xboole_0 ) )
     => ( A = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X245: $i] :
      ( ( X245 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X245 @ k1_xboole_0 ) ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('6',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,(
    ! [X245: $i] :
      ( ( X245 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X245 @ o_0_0_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    sk_A_5 = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    sk_A_5 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('12',plain,(
    sk_A_5 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['9','12'])).

%------------------------------------------------------------------------------

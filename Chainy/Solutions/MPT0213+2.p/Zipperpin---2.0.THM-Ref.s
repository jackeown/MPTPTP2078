%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0213+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gu4wd50i78

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:49 EST 2020

% Result     : Theorem 13.07s
% Output     : Refutation 13.07s
% Verified   : 
% Statistics : Number of formulae       :   34 (  53 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :  135 ( 219 expanded)
%              Number of equality atoms :   17 (  30 expanded)
%              Maximal formula depth    :   12 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_D_7_type,type,(
    sk_D_7: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_7_type,type,(
    sk_C_7: $i > $i > $i )).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ? [D: $i] :
              ( ( r2_hidden @ ( D @ A ) )
              & ( r2_hidden @ ( C @ D ) ) ) ) ) )).

thf('0',plain,(
    ! [X966: $i,X970: $i] :
      ( ( X970
        = ( k3_tarski @ X966 ) )
      | ( r2_hidden @ ( sk_D_7 @ ( X970 @ X966 ) @ X966 ) )
      | ( r2_hidden @ ( sk_C_7 @ ( X970 @ X966 ) @ X970 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ ( A @ k1_xboole_0 ) )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X215: $i] :
      ( ( k3_xboole_0 @ ( X215 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('4',plain,(
    ! [X215: $i] :
      ( ( k3_xboole_0 @ ( X215 @ o_0_0_xboole_0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ ( C @ ( k3_xboole_0 @ ( A @ B ) ) ) )
          & ( r1_xboole_0 @ ( A @ B ) ) )
      & ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ ( C @ ( k3_xboole_0 @ ( A @ B ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X62: $i,X64: $i,X65: $i] :
      ( ~ ( r2_hidden @ ( X64 @ ( k3_xboole_0 @ ( X62 @ X65 ) ) ) )
      | ~ ( r1_xboole_0 @ ( X62 @ X65 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( X1 @ o_0_0_xboole_0 ) )
      | ~ ( r1_xboole_0 @ ( X0 @ o_0_0_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ ( A @ k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X317: $i] :
      ( r1_xboole_0 @ ( X317 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,(
    ! [X317: $i] :
      ( r1_xboole_0 @ ( X317 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ ( X1 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_7 @ ( o_0_0_xboole_0 @ X0 ) @ X0 ) )
      | ( o_0_0_xboole_0
        = ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ ( X1 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('13',plain,
    ( o_0_0_xboole_0
    = ( k3_tarski @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t2_zfmisc_1,conjecture,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k3_tarski @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t2_zfmisc_1])).

thf('14',plain,(
    ( k3_tarski @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('17',plain,(
    ( k3_tarski @ o_0_0_xboole_0 )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['13','17'])).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0064+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ry4Ct9W4Zj

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   11 (  13 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    4
%              Number of atoms          :   34 (  46 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t57_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ ( A @ B ) )
        & ( r2_xboole_0 @ ( B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( r2_xboole_0 @ ( A @ B ) )
          & ( r2_xboole_0 @ ( B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_xboole_1])).

thf('0',plain,(
    r2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(antisymmetry_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ ( A @ B ) )
     => ~ ( r2_xboole_0 @ ( B @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_xboole_0 @ ( X2 @ X3 ) )
      | ~ ( r2_xboole_0 @ ( X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_xboole_0])).

thf('2',plain,(
    ~ ( r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    $false ),
    inference(demod,[status(thm)],['2','3'])).

%------------------------------------------------------------------------------

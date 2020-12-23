%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0231+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.04IgchUHWA

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:50 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   27 (  29 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  139 ( 157 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_C_8_type,type,(
    sk_C_8: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A @ ( k2_tarski @ ( A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X1004: $i,X1005: $i] :
      ( r1_tarski @ ( k1_tarski @ X1004 @ ( k2_tarski @ ( X1004 @ X1005 ) ) ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t26_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ ( A @ B ) @ ( k1_tarski @ C ) ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ ( A @ B ) @ ( k1_tarski @ C ) ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t26_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ ( k1_tarski @ sk_C_8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('2',plain,(
    ! [X210: $i,X211: $i] :
      ( ( ( k3_xboole_0 @ ( X210 @ X211 ) )
        = X210 )
      | ~ ( r1_tarski @ ( X210 @ X211 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ ( k1_tarski @ sk_C_8 ) ) )
    = ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_C_8 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) )
    = ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
     => ( r1_tarski @ ( A @ B ) ) ) )).

thf('6',plain,(
    ! [X177: $i,X178: $i,X179: $i] :
      ( ( r1_tarski @ ( X177 @ X178 ) )
      | ~ ( r1_tarski @ ( X177 @ ( k3_xboole_0 @ ( X178 @ X179 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( X0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) )
      | ( r1_tarski @ ( X0 @ ( k1_tarski @ sk_C_8 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_C_8 ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf(t24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) )
     => ( A = B ) ) )).

thf('9',plain,(
    ! [X1027: $i,X1028: $i] :
      ( ( X1028 = X1027 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1028 @ ( k1_tarski @ X1027 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_zfmisc_1])).

thf('10',plain,(
    sk_A_2 = sk_C_8 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    sk_A_2 != sk_C_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0314+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Tq7eSeylm2

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:41 EST 2020

% Result     : Theorem 12.08s
% Output     : Refutation 12.08s
% Verified   : 
% Statistics : Number of formulae       :   54 (  66 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  516 ( 654 expanded)
%              Number of equality atoms :   40 (  51 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t126_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ C ) @ B ) @ ( k2_zfmisc_1 @ A @ ( k4_xboole_0 @ B @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ C ) @ B ) @ ( k2_zfmisc_1 @ A @ ( k4_xboole_0 @ B @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t126_zfmisc_1])).

thf('0',plain,(
    ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D_2 ) )
 != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_D_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ( k2_zfmisc_1 @ X23 @ ( k4_xboole_0 @ X20 @ X22 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X23 @ X20 ) @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X20 @ X22 ) @ X21 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf(t54_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k3_xboole_0 @ X27 @ X28 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X26 @ X27 ) @ ( k4_xboole_0 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t54_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X3 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X2 @ X3 ) @ X1 ) @ ( k2_zfmisc_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X16 @ X18 ) @ ( k3_xboole_0 @ X17 @ X19 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X2 @ X3 ) @ X1 ) @ ( k2_zfmisc_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D_2 ) )
 != ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D_2 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','7','8'])).

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X16 @ X18 ) @ ( k3_xboole_0 @ X17 @ X19 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i,X15: $i] :
      ( ( X15
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ( r2_hidden @ ( sk_D_1 @ X15 @ X12 @ X11 ) @ X11 )
      | ( r2_hidden @ ( sk_D_1 @ X15 @ X12 @ X11 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X25: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('13',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ( X13
       != ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('14',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X11: $i,X12: $i,X15: $i] :
      ( ( X15
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X15 @ X12 @ X11 ) @ X12 )
      | ( r2_hidden @ ( sk_D_1 @ X15 @ X12 @ X11 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['15'])).

thf('22',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k3_xboole_0 @ X27 @ X28 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X26 @ X27 ) @ ( k4_xboole_0 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t54_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X24: $i] :
      ( ( k2_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','29'])).

thf('31',plain,(
    ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D_2 ) )
 != ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['9','30'])).

thf('32',plain,(
    $false ),
    inference(simplify,[status(thm)],['31'])).


%------------------------------------------------------------------------------

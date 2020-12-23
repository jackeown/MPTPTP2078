%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uh4pYeh4Rt

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:11 EST 2020

% Result     : Theorem 1.91s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 122 expanded)
%              Number of leaves         :   23 (  44 expanded)
%              Depth                    :   21
%              Number of atoms          :  835 (1159 expanded)
%              Number of equality atoms :   80 ( 116 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k4_xboole_0 @ X39 @ ( k1_tarski @ X40 ) )
        = X39 )
      | ( r2_hidden @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r1_xboole_0 @ X17 @ X19 )
      | ( ( k4_xboole_0 @ X17 @ X19 )
       != X17 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t87_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ X20 @ X21 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X22 @ X20 ) @ X21 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X22 @ X21 ) @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t87_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t147_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( A != B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( A != B )
       => ( ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) )
          = ( k2_xboole_0 @ ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t147_zfmisc_1])).

thf('6',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) )
 != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) )
     != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) )
     != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['15','28'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('30',plain,(
    ! [X29: $i,X31: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X29 ) @ X31 )
        = ( k1_tarski @ X29 ) )
      | ( r2_hidden @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('33',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('34',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k4_xboole_0 @ X39 @ ( k1_tarski @ X40 ) )
        = X39 )
      | ( r2_hidden @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('35',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k4_xboole_0 @ X39 @ ( k1_tarski @ X40 ) )
        = X39 )
      | ( r2_hidden @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('36',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) )
 != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('37',plain,
    ( ( ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) )
     != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
    | ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) )
     != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C ) )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('40',plain,
    ( ( ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) )
     != ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('42',plain,(
    ! [X34: $i,X35: $i,X37: $i] :
      ( ( r2_hidden @ X34 @ ( k4_xboole_0 @ X35 @ ( k1_tarski @ X37 ) ) )
      | ( X34 = X37 )
      | ~ ( r2_hidden @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ sk_C )
      | ( sk_B = X0 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['33','43'])).

thf('45',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('47',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('48',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X34: $i,X35: $i,X37: $i] :
      ( ( r2_hidden @ X34 @ ( k4_xboole_0 @ X35 @ ( k1_tarski @ X37 ) ) )
      | ( X34 = X37 )
      | ~ ( r2_hidden @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X34: $i,X35: $i,X37: $i] :
      ( ( r2_hidden @ X34 @ ( k4_xboole_0 @ X35 @ ( k1_tarski @ X37 ) ) )
      | ( X34 = X37 )
      | ~ ( r2_hidden @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B = X0 )
      | ( sk_B = X1 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B = X0 )
      | ( sk_B = X1 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('57',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B = X0 )
      | ( sk_B = X1 )
      | ~ ( r2_hidden @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ ( k3_tarski @ ( k1_tarski @ ( k1_tarski @ X0 ) ) ) )
      | ( sk_B = X0 )
      | ( sk_B = X0 ) ) ),
    inference('sup-',[status(thm)],['32','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ~ ( r2_hidden @ sk_B @ ( k3_tarski @ ( k1_tarski @ ( k1_tarski @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ sk_B ) )
      | ( sk_B = X0 ) ) ),
    inference('sup-',[status(thm)],['31','60'])).

thf('62',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34 != X36 )
      | ~ ( r2_hidden @ X34 @ ( k4_xboole_0 @ X35 @ ( k1_tarski @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('63',plain,(
    ! [X35: $i,X36: $i] :
      ~ ( r2_hidden @ X36 @ ( k4_xboole_0 @ X35 @ ( k1_tarski @ X36 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ( sk_B = X0 ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['12','64'])).

thf('66',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uh4pYeh4Rt
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:13:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.91/2.09  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.91/2.09  % Solved by: fo/fo7.sh
% 1.91/2.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.91/2.09  % done 2786 iterations in 1.639s
% 1.91/2.09  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.91/2.09  % SZS output start Refutation
% 1.91/2.09  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.91/2.09  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.91/2.09  thf(sk_A_type, type, sk_A: $i).
% 1.91/2.09  thf(sk_B_type, type, sk_B: $i).
% 1.91/2.09  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.91/2.09  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.91/2.09  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.91/2.09  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.91/2.09  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.91/2.09  thf(sk_C_type, type, sk_C: $i).
% 1.91/2.09  thf(t65_zfmisc_1, axiom,
% 1.91/2.09    (![A:$i,B:$i]:
% 1.91/2.09     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.91/2.09       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.91/2.09  thf('0', plain,
% 1.91/2.09      (![X39 : $i, X40 : $i]:
% 1.91/2.09         (((k4_xboole_0 @ X39 @ (k1_tarski @ X40)) = (X39))
% 1.91/2.09          | (r2_hidden @ X40 @ X39))),
% 1.91/2.09      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 1.91/2.09  thf(t83_xboole_1, axiom,
% 1.91/2.09    (![A:$i,B:$i]:
% 1.91/2.09     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.91/2.09  thf('1', plain,
% 1.91/2.09      (![X17 : $i, X19 : $i]:
% 1.91/2.09         ((r1_xboole_0 @ X17 @ X19) | ((k4_xboole_0 @ X17 @ X19) != (X17)))),
% 1.91/2.09      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.91/2.09  thf('2', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         (((X0) != (X0))
% 1.91/2.09          | (r2_hidden @ X1 @ X0)
% 1.91/2.09          | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['0', '1'])).
% 1.91/2.09  thf('3', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 1.91/2.09      inference('simplify', [status(thm)], ['2'])).
% 1.91/2.09  thf(t87_xboole_1, axiom,
% 1.91/2.09    (![A:$i,B:$i,C:$i]:
% 1.91/2.09     ( ( r1_xboole_0 @ A @ B ) =>
% 1.91/2.09       ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B ) =
% 1.91/2.09         ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ))).
% 1.91/2.09  thf('4', plain,
% 1.91/2.09      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.91/2.09         (~ (r1_xboole_0 @ X20 @ X21)
% 1.91/2.09          | ((k2_xboole_0 @ (k4_xboole_0 @ X22 @ X20) @ X21)
% 1.91/2.09              = (k4_xboole_0 @ (k2_xboole_0 @ X22 @ X21) @ X20)))),
% 1.91/2.09      inference('cnf', [status(esa)], [t87_xboole_1])).
% 1.91/2.09  thf('5', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.09         ((r2_hidden @ X0 @ X1)
% 1.91/2.09          | ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k1_tarski @ X0))
% 1.91/2.09              = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k1_tarski @ X0)) @ X1)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['3', '4'])).
% 1.91/2.09  thf(t147_zfmisc_1, conjecture,
% 1.91/2.09    (![A:$i,B:$i,C:$i]:
% 1.91/2.09     ( ( ( A ) != ( B ) ) =>
% 1.91/2.09       ( ( k4_xboole_0 @
% 1.91/2.09           ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) ) =
% 1.91/2.09         ( k2_xboole_0 @
% 1.91/2.09           ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ))).
% 1.91/2.09  thf(zf_stmt_0, negated_conjecture,
% 1.91/2.09    (~( ![A:$i,B:$i,C:$i]:
% 1.91/2.09        ( ( ( A ) != ( B ) ) =>
% 1.91/2.09          ( ( k4_xboole_0 @
% 1.91/2.09              ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) ) =
% 1.91/2.09            ( k2_xboole_0 @
% 1.91/2.09              ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) )),
% 1.91/2.09    inference('cnf.neg', [status(esa)], [t147_zfmisc_1])).
% 1.91/2.09  thf('6', plain,
% 1.91/2.09      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 1.91/2.09         (k1_tarski @ sk_B))
% 1.91/2.09         != (k2_xboole_0 @ (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B)) @ 
% 1.91/2.09             (k1_tarski @ sk_A)))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf(commutativity_k2_xboole_0, axiom,
% 1.91/2.09    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.91/2.09  thf('7', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.91/2.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.91/2.09  thf('8', plain,
% 1.91/2.09      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 1.91/2.09         (k1_tarski @ sk_B))
% 1.91/2.09         != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.91/2.09             (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B))))),
% 1.91/2.09      inference('demod', [status(thm)], ['6', '7'])).
% 1.91/2.09  thf('9', plain,
% 1.91/2.09      ((((k2_xboole_0 @ (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B)) @ 
% 1.91/2.09          (k1_tarski @ sk_A))
% 1.91/2.09          != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.91/2.09              (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B))))
% 1.91/2.09        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['5', '8'])).
% 1.91/2.09  thf('10', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.91/2.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.91/2.09  thf('11', plain,
% 1.91/2.09      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.91/2.09          (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B)))
% 1.91/2.09          != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.91/2.09              (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B))))
% 1.91/2.09        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 1.91/2.09      inference('demod', [status(thm)], ['9', '10'])).
% 1.91/2.09  thf('12', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 1.91/2.09      inference('simplify', [status(thm)], ['11'])).
% 1.91/2.09  thf(t69_enumset1, axiom,
% 1.91/2.09    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.91/2.09  thf('13', plain,
% 1.91/2.09      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 1.91/2.09      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.91/2.09  thf(l51_zfmisc_1, axiom,
% 1.91/2.09    (![A:$i,B:$i]:
% 1.91/2.09     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.91/2.09  thf('14', plain,
% 1.91/2.09      (![X32 : $i, X33 : $i]:
% 1.91/2.09         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 1.91/2.09      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.91/2.09  thf('15', plain,
% 1.91/2.09      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 1.91/2.09      inference('sup+', [status(thm)], ['13', '14'])).
% 1.91/2.09  thf(t40_xboole_1, axiom,
% 1.91/2.09    (![A:$i,B:$i]:
% 1.91/2.09     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.91/2.09  thf('16', plain,
% 1.91/2.09      (![X12 : $i, X13 : $i]:
% 1.91/2.09         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 1.91/2.09           = (k4_xboole_0 @ X12 @ X13))),
% 1.91/2.09      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.91/2.09  thf(t39_xboole_1, axiom,
% 1.91/2.09    (![A:$i,B:$i]:
% 1.91/2.09     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.91/2.09  thf('17', plain,
% 1.91/2.09      (![X10 : $i, X11 : $i]:
% 1.91/2.09         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 1.91/2.09           = (k2_xboole_0 @ X10 @ X11))),
% 1.91/2.09      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.91/2.09  thf('18', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.91/2.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.91/2.09  thf('19', plain,
% 1.91/2.09      (![X12 : $i, X13 : $i]:
% 1.91/2.09         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 1.91/2.09           = (k4_xboole_0 @ X12 @ X13))),
% 1.91/2.09      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.91/2.09  thf('20', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.91/2.09           = (k4_xboole_0 @ X0 @ X1))),
% 1.91/2.09      inference('sup+', [status(thm)], ['18', '19'])).
% 1.91/2.09  thf('21', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.91/2.09           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 1.91/2.09      inference('sup+', [status(thm)], ['17', '20'])).
% 1.91/2.09  thf('22', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.91/2.09           = (k4_xboole_0 @ X0 @ X1))),
% 1.91/2.09      inference('sup+', [status(thm)], ['18', '19'])).
% 1.91/2.09  thf('23', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         ((k4_xboole_0 @ X0 @ X1)
% 1.91/2.09           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 1.91/2.09      inference('demod', [status(thm)], ['21', '22'])).
% 1.91/2.09  thf('24', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 1.91/2.09           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.91/2.09      inference('sup+', [status(thm)], ['16', '23'])).
% 1.91/2.09  thf('25', plain,
% 1.91/2.09      (![X12 : $i, X13 : $i]:
% 1.91/2.09         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 1.91/2.09           = (k4_xboole_0 @ X12 @ X13))),
% 1.91/2.09      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.91/2.09  thf('26', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         ((k4_xboole_0 @ X1 @ X0)
% 1.91/2.09           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.91/2.09      inference('demod', [status(thm)], ['24', '25'])).
% 1.91/2.09  thf(t41_xboole_1, axiom,
% 1.91/2.09    (![A:$i,B:$i,C:$i]:
% 1.91/2.09     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.91/2.09       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.91/2.09  thf('27', plain,
% 1.91/2.09      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.91/2.09         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 1.91/2.09           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 1.91/2.09      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.91/2.09  thf('28', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         ((k4_xboole_0 @ X1 @ X0)
% 1.91/2.09           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0)))),
% 1.91/2.09      inference('demod', [status(thm)], ['26', '27'])).
% 1.91/2.09  thf('29', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         ((k4_xboole_0 @ X1 @ X0)
% 1.91/2.09           = (k4_xboole_0 @ X1 @ (k3_tarski @ (k1_tarski @ X0))))),
% 1.91/2.09      inference('sup+', [status(thm)], ['15', '28'])).
% 1.91/2.09  thf(l33_zfmisc_1, axiom,
% 1.91/2.09    (![A:$i,B:$i]:
% 1.91/2.09     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 1.91/2.09       ( ~( r2_hidden @ A @ B ) ) ))).
% 1.91/2.09  thf('30', plain,
% 1.91/2.09      (![X29 : $i, X31 : $i]:
% 1.91/2.09         (((k4_xboole_0 @ (k1_tarski @ X29) @ X31) = (k1_tarski @ X29))
% 1.91/2.09          | (r2_hidden @ X29 @ X31))),
% 1.91/2.09      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 1.91/2.09  thf('31', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1))
% 1.91/2.09          | (r2_hidden @ X1 @ (k3_tarski @ (k1_tarski @ X0))))),
% 1.91/2.09      inference('sup+', [status(thm)], ['29', '30'])).
% 1.91/2.09  thf('32', plain,
% 1.91/2.09      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 1.91/2.09      inference('sup+', [status(thm)], ['13', '14'])).
% 1.91/2.09  thf('33', plain,
% 1.91/2.09      (![X12 : $i, X13 : $i]:
% 1.91/2.09         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13)
% 1.91/2.09           = (k4_xboole_0 @ X12 @ X13))),
% 1.91/2.09      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.91/2.09  thf('34', plain,
% 1.91/2.09      (![X39 : $i, X40 : $i]:
% 1.91/2.09         (((k4_xboole_0 @ X39 @ (k1_tarski @ X40)) = (X39))
% 1.91/2.09          | (r2_hidden @ X40 @ X39))),
% 1.91/2.09      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 1.91/2.09  thf('35', plain,
% 1.91/2.09      (![X39 : $i, X40 : $i]:
% 1.91/2.09         (((k4_xboole_0 @ X39 @ (k1_tarski @ X40)) = (X39))
% 1.91/2.09          | (r2_hidden @ X40 @ X39))),
% 1.91/2.09      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 1.91/2.09  thf('36', plain,
% 1.91/2.09      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 1.91/2.09         (k1_tarski @ sk_B))
% 1.91/2.09         != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.91/2.09             (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B))))),
% 1.91/2.09      inference('demod', [status(thm)], ['6', '7'])).
% 1.91/2.09  thf('37', plain,
% 1.91/2.09      ((((k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A))
% 1.91/2.09          != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.91/2.09              (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B))))
% 1.91/2.09        | (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A))))),
% 1.91/2.09      inference('sup-', [status(thm)], ['35', '36'])).
% 1.91/2.09  thf('38', plain,
% 1.91/2.09      ((((k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A))
% 1.91/2.09          != (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_C))
% 1.91/2.09        | (r2_hidden @ sk_B @ sk_C)
% 1.91/2.09        | (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A))))),
% 1.91/2.09      inference('sup-', [status(thm)], ['34', '37'])).
% 1.91/2.09  thf('39', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.91/2.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.91/2.09  thf('40', plain,
% 1.91/2.09      ((((k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A))
% 1.91/2.09          != (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)))
% 1.91/2.09        | (r2_hidden @ sk_B @ sk_C)
% 1.91/2.09        | (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A))))),
% 1.91/2.09      inference('demod', [status(thm)], ['38', '39'])).
% 1.91/2.09  thf('41', plain,
% 1.91/2.09      (((r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)))
% 1.91/2.09        | (r2_hidden @ sk_B @ sk_C))),
% 1.91/2.09      inference('simplify', [status(thm)], ['40'])).
% 1.91/2.09  thf(t64_zfmisc_1, axiom,
% 1.91/2.09    (![A:$i,B:$i,C:$i]:
% 1.91/2.09     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 1.91/2.09       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 1.91/2.09  thf('42', plain,
% 1.91/2.09      (![X34 : $i, X35 : $i, X37 : $i]:
% 1.91/2.09         ((r2_hidden @ X34 @ (k4_xboole_0 @ X35 @ (k1_tarski @ X37)))
% 1.91/2.09          | ((X34) = (X37))
% 1.91/2.09          | ~ (r2_hidden @ X34 @ X35))),
% 1.91/2.09      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 1.91/2.09  thf('43', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((r2_hidden @ sk_B @ sk_C)
% 1.91/2.09          | ((sk_B) = (X0))
% 1.91/2.09          | (r2_hidden @ sk_B @ 
% 1.91/2.09             (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 1.91/2.09              (k1_tarski @ X0))))),
% 1.91/2.09      inference('sup-', [status(thm)], ['41', '42'])).
% 1.91/2.09  thf('44', plain,
% 1.91/2.09      (((r2_hidden @ sk_B @ (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_A)))
% 1.91/2.09        | ((sk_B) = (sk_A))
% 1.91/2.09        | (r2_hidden @ sk_B @ sk_C))),
% 1.91/2.09      inference('sup+', [status(thm)], ['33', '43'])).
% 1.91/2.09  thf('45', plain, (((sk_A) != (sk_B))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('46', plain,
% 1.91/2.09      (((r2_hidden @ sk_B @ (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_A)))
% 1.91/2.09        | (r2_hidden @ sk_B @ sk_C))),
% 1.91/2.09      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 1.91/2.09  thf(d5_xboole_0, axiom,
% 1.91/2.09    (![A:$i,B:$i,C:$i]:
% 1.91/2.09     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.91/2.09       ( ![D:$i]:
% 1.91/2.09         ( ( r2_hidden @ D @ C ) <=>
% 1.91/2.09           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.91/2.09  thf('47', plain,
% 1.91/2.09      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.91/2.09         (~ (r2_hidden @ X6 @ X5)
% 1.91/2.09          | (r2_hidden @ X6 @ X3)
% 1.91/2.09          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.91/2.09      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.91/2.09  thf('48', plain,
% 1.91/2.09      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.91/2.09         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.91/2.09      inference('simplify', [status(thm)], ['47'])).
% 1.91/2.09  thf('49', plain, ((r2_hidden @ sk_B @ sk_C)),
% 1.91/2.09      inference('clc', [status(thm)], ['46', '48'])).
% 1.91/2.09  thf('50', plain,
% 1.91/2.09      (![X34 : $i, X35 : $i, X37 : $i]:
% 1.91/2.09         ((r2_hidden @ X34 @ (k4_xboole_0 @ X35 @ (k1_tarski @ X37)))
% 1.91/2.09          | ((X34) = (X37))
% 1.91/2.09          | ~ (r2_hidden @ X34 @ X35))),
% 1.91/2.09      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 1.91/2.09  thf('51', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (((sk_B) = (X0))
% 1.91/2.09          | (r2_hidden @ sk_B @ (k4_xboole_0 @ sk_C @ (k1_tarski @ X0))))),
% 1.91/2.09      inference('sup-', [status(thm)], ['49', '50'])).
% 1.91/2.09  thf('52', plain,
% 1.91/2.09      (![X34 : $i, X35 : $i, X37 : $i]:
% 1.91/2.09         ((r2_hidden @ X34 @ (k4_xboole_0 @ X35 @ (k1_tarski @ X37)))
% 1.91/2.09          | ((X34) = (X37))
% 1.91/2.09          | ~ (r2_hidden @ X34 @ X35))),
% 1.91/2.09      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 1.91/2.09  thf('53', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         (((sk_B) = (X0))
% 1.91/2.09          | ((sk_B) = (X1))
% 1.91/2.09          | (r2_hidden @ sk_B @ 
% 1.91/2.09             (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ (k1_tarski @ X0)) @ 
% 1.91/2.09              (k1_tarski @ X1))))),
% 1.91/2.09      inference('sup-', [status(thm)], ['51', '52'])).
% 1.91/2.09  thf('54', plain,
% 1.91/2.09      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.91/2.09         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 1.91/2.09           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 1.91/2.09      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.91/2.09  thf('55', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         (((sk_B) = (X0))
% 1.91/2.09          | ((sk_B) = (X1))
% 1.91/2.09          | (r2_hidden @ sk_B @ 
% 1.91/2.09             (k4_xboole_0 @ sk_C @ 
% 1.91/2.09              (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))))),
% 1.91/2.09      inference('demod', [status(thm)], ['53', '54'])).
% 1.91/2.09  thf('56', plain,
% 1.91/2.09      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.91/2.09         (~ (r2_hidden @ X6 @ X5)
% 1.91/2.09          | ~ (r2_hidden @ X6 @ X4)
% 1.91/2.09          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.91/2.09      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.91/2.09  thf('57', plain,
% 1.91/2.09      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.91/2.09         (~ (r2_hidden @ X6 @ X4)
% 1.91/2.09          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.91/2.09      inference('simplify', [status(thm)], ['56'])).
% 1.91/2.09  thf('58', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         (((sk_B) = (X0))
% 1.91/2.09          | ((sk_B) = (X1))
% 1.91/2.09          | ~ (r2_hidden @ sk_B @ 
% 1.91/2.09               (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))))),
% 1.91/2.09      inference('sup-', [status(thm)], ['55', '57'])).
% 1.91/2.09  thf('59', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (~ (r2_hidden @ sk_B @ (k3_tarski @ (k1_tarski @ (k1_tarski @ X0))))
% 1.91/2.09          | ((sk_B) = (X0))
% 1.91/2.09          | ((sk_B) = (X0)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['32', '58'])).
% 1.91/2.09  thf('60', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (((sk_B) = (X0))
% 1.91/2.09          | ~ (r2_hidden @ sk_B @ (k3_tarski @ (k1_tarski @ (k1_tarski @ X0)))))),
% 1.91/2.09      inference('simplify', [status(thm)], ['59'])).
% 1.91/2.09  thf('61', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ X0))
% 1.91/2.09            = (k1_tarski @ sk_B))
% 1.91/2.09          | ((sk_B) = (X0)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['31', '60'])).
% 1.91/2.09  thf('62', plain,
% 1.91/2.09      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.91/2.09         (((X34) != (X36))
% 1.91/2.09          | ~ (r2_hidden @ X34 @ (k4_xboole_0 @ X35 @ (k1_tarski @ X36))))),
% 1.91/2.09      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 1.91/2.09  thf('63', plain,
% 1.91/2.09      (![X35 : $i, X36 : $i]:
% 1.91/2.09         ~ (r2_hidden @ X36 @ (k4_xboole_0 @ X35 @ (k1_tarski @ X36)))),
% 1.91/2.09      inference('simplify', [status(thm)], ['62'])).
% 1.91/2.09  thf('64', plain,
% 1.91/2.09      (![X0 : $i]: (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B)) | ((sk_B) = (X0)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['61', '63'])).
% 1.91/2.09  thf('65', plain, (((sk_B) = (sk_A))),
% 1.91/2.09      inference('sup-', [status(thm)], ['12', '64'])).
% 1.91/2.09  thf('66', plain, (((sk_A) != (sk_B))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('67', plain, ($false),
% 1.91/2.09      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 1.91/2.09  
% 1.91/2.09  % SZS output end Refutation
% 1.91/2.09  
% 1.91/2.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

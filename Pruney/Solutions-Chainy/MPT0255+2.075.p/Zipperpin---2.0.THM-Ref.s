%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jpm5k8Xsfj

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:05 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 385 expanded)
%              Number of leaves         :   19 ( 117 expanded)
%              Depth                    :   26
%              Number of atoms          :  908 (4690 expanded)
%              Number of equality atoms :   54 ( 313 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('2',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','8'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('11',plain,(
    ! [X14: $i] :
      ( r1_xboole_0 @ X14 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('12',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('13',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','8'])).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('15',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ sk_C_1 )
      | ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ sk_C_1 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = X0 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['19'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ sk_C_1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ sk_C_1 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('25',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ sk_C_1 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ ( k2_xboole_0 @ X1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ sk_C_1 )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['10','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('29',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ ( k2_xboole_0 @ sk_C_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['9','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('38',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('42',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['39','40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['36','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ sk_A @ sk_B )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X14: $i] :
      ( r1_xboole_0 @ X14 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('51',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','51'])).

thf('53',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('54',plain,
    ( k1_xboole_0
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('55',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ ( k2_tarski @ X19 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('57',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ sk_A @ sk_B )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('60',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference('sup-',[status(thm)],['58','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jpm5k8Xsfj
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 213 iterations in 0.200s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.65  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.65  thf(d3_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.45/0.65       ( ![D:$i]:
% 0.45/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.65           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.45/0.65         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.45/0.65          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.45/0.65          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 0.45/0.65          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.45/0.65          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.45/0.65          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.45/0.65      inference('eq_fact', [status(thm)], ['0'])).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.45/0.65         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.45/0.65          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.45/0.65          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 0.45/0.65          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.45/0.65          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.45/0.65          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.45/0.65          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.45/0.65          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['3'])).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.45/0.65          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.45/0.65          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.45/0.65      inference('eq_fact', [status(thm)], ['0'])).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 0.45/0.65          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.45/0.65      inference('clc', [status(thm)], ['4', '5'])).
% 0.45/0.65  thf(t50_zfmisc_1, conjecture,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.65        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(commutativity_k2_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      (((k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['7', '8'])).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      (((k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['7', '8'])).
% 0.45/0.65  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.45/0.65  thf('11', plain, (![X14 : $i]: (r1_xboole_0 @ X14 @ k1_xboole_0)),
% 0.45/0.65      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.45/0.65         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.45/0.65          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.45/0.65          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 0.45/0.65          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      (((k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['7', '8'])).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X6 @ X4)
% 0.45/0.65          | (r2_hidden @ X6 @ X5)
% 0.45/0.65          | (r2_hidden @ X6 @ X3)
% 0.45/0.65          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.45/0.65         ((r2_hidden @ X6 @ X3)
% 0.45/0.65          | (r2_hidden @ X6 @ X5)
% 0.45/0.65          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['14'])).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.45/0.65          | (r2_hidden @ X0 @ sk_C_1)
% 0.45/0.65          | (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['13', '15'])).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.45/0.65          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X0)
% 0.45/0.65          | ((X1) = (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.45/0.65          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ 
% 0.45/0.65             (k2_tarski @ sk_A @ sk_B))
% 0.45/0.65          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ sk_C_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['12', '16'])).
% 0.45/0.65  thf(t1_boole, axiom,
% 0.45/0.65    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.65  thf('18', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.45/0.65      inference('cnf', [status(esa)], [t1_boole])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.45/0.65          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X0)
% 0.45/0.65          | ((X1) = (X0))
% 0.45/0.65          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ 
% 0.45/0.65             (k2_tarski @ sk_A @ sk_B))
% 0.45/0.65          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ sk_C_1))),
% 0.45/0.65      inference('demod', [status(thm)], ['17', '18'])).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.45/0.65           sk_C_1)
% 0.45/0.65          | (r2_hidden @ 
% 0.45/0.65             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.45/0.65             (k2_tarski @ sk_A @ sk_B))
% 0.45/0.65          | ((k2_tarski @ sk_A @ sk_B) = (X0))
% 0.45/0.65          | (r2_hidden @ 
% 0.45/0.65             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ X0))),
% 0.45/0.65      inference('eq_fact', [status(thm)], ['19'])).
% 0.45/0.65  thf(t4_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.65            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.45/0.65          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.45/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.65  thf('22', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((k2_tarski @ sk_A @ sk_B) = (k3_xboole_0 @ X1 @ X0))
% 0.45/0.65          | (r2_hidden @ 
% 0.45/0.65             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ 
% 0.45/0.65              (k3_xboole_0 @ X1 @ X0)) @ 
% 0.45/0.65             (k2_tarski @ sk_A @ sk_B))
% 0.45/0.65          | (r2_hidden @ 
% 0.45/0.65             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ 
% 0.45/0.65              (k3_xboole_0 @ X1 @ X0)) @ 
% 0.45/0.65             sk_C_1)
% 0.45/0.65          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.65  thf('23', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((r2_hidden @ 
% 0.45/0.65           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ 
% 0.45/0.65            (k3_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.45/0.65           sk_C_1)
% 0.45/0.65          | (r2_hidden @ 
% 0.45/0.65             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ 
% 0.45/0.65              (k3_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.45/0.65             (k2_tarski @ sk_A @ sk_B))
% 0.45/0.65          | ((k2_tarski @ sk_A @ sk_B) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['11', '22'])).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X2 @ X3)
% 0.45/0.65          | (r2_hidden @ X2 @ X4)
% 0.45/0.65          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.45/0.65  thf('25', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.45/0.65         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.45/0.65      inference('simplify', [status(thm)], ['24'])).
% 0.45/0.65  thf('26', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((k2_tarski @ sk_A @ sk_B) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 0.45/0.65          | (r2_hidden @ 
% 0.45/0.65             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ 
% 0.45/0.65              (k3_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.45/0.65             sk_C_1)
% 0.45/0.65          | (r2_hidden @ 
% 0.45/0.65             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ 
% 0.45/0.65              (k3_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.45/0.65             (k2_xboole_0 @ X1 @ (k2_tarski @ sk_A @ sk_B))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['23', '25'])).
% 0.45/0.65  thf('27', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((r2_hidden @ 
% 0.45/0.65           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ 
% 0.45/0.65            (k3_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.45/0.65           k1_xboole_0)
% 0.45/0.65          | (r2_hidden @ 
% 0.45/0.65             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ 
% 0.45/0.65              (k3_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.45/0.65             sk_C_1)
% 0.45/0.65          | ((k2_tarski @ sk_A @ sk_B) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['10', '26'])).
% 0.45/0.65  thf('28', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X2 @ X5)
% 0.45/0.65          | (r2_hidden @ X2 @ X4)
% 0.45/0.65          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.45/0.65  thf('29', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.45/0.65         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 0.45/0.65      inference('simplify', [status(thm)], ['28'])).
% 0.45/0.65  thf('30', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((k2_tarski @ sk_A @ sk_B) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 0.45/0.65          | (r2_hidden @ 
% 0.45/0.65             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ 
% 0.45/0.65              (k3_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.45/0.65             k1_xboole_0)
% 0.45/0.65          | (r2_hidden @ 
% 0.45/0.65             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ 
% 0.45/0.65              (k3_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.45/0.65             (k2_xboole_0 @ sk_C_1 @ X1)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['27', '29'])).
% 0.45/0.65  thf('31', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((r2_hidden @ 
% 0.45/0.65           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ 
% 0.45/0.65            (k3_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.45/0.65           k1_xboole_0)
% 0.45/0.65          | (r2_hidden @ 
% 0.45/0.65             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ 
% 0.45/0.65              (k3_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.45/0.65             k1_xboole_0)
% 0.45/0.65          | ((k2_tarski @ sk_A @ sk_B) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['9', '30'])).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k2_tarski @ sk_A @ sk_B) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 0.45/0.65          | (r2_hidden @ 
% 0.45/0.65             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ 
% 0.45/0.65              (k3_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.45/0.65             k1_xboole_0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['31'])).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.45/0.65         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.48/0.65      inference('simplify', [status(thm)], ['24'])).
% 0.48/0.65  thf('34', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i]:
% 0.48/0.65         (((k2_tarski @ sk_A @ sk_B) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 0.48/0.65          | (r2_hidden @ 
% 0.48/0.65             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ 
% 0.48/0.65              (k3_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.48/0.65             (k2_xboole_0 @ X1 @ k1_xboole_0)))),
% 0.48/0.65      inference('sup-', [status(thm)], ['32', '33'])).
% 0.48/0.65  thf('35', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.48/0.65      inference('cnf', [status(esa)], [t1_boole])).
% 0.48/0.65  thf('36', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i]:
% 0.48/0.65         (((k2_tarski @ sk_A @ sk_B) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 0.48/0.65          | (r2_hidden @ 
% 0.48/0.65             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ 
% 0.48/0.65              (k3_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.48/0.65             X1))),
% 0.48/0.65      inference('demod', [status(thm)], ['34', '35'])).
% 0.48/0.65  thf('37', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         (((k2_tarski @ sk_A @ sk_B) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 0.48/0.65          | (r2_hidden @ 
% 0.48/0.65             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ 
% 0.48/0.65              (k3_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.48/0.65             k1_xboole_0))),
% 0.48/0.65      inference('simplify', [status(thm)], ['31'])).
% 0.48/0.65  thf('38', plain,
% 0.48/0.65      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.48/0.65         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.48/0.65          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.48/0.65          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.48/0.65      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.48/0.65  thf('39', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         (((k2_tarski @ sk_A @ sk_B) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 0.48/0.65          | ~ (r2_hidden @ 
% 0.48/0.65               (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ 
% 0.48/0.65                (k3_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.48/0.65               (k2_tarski @ sk_A @ sk_B))
% 0.48/0.65          | ((k2_tarski @ sk_A @ sk_B)
% 0.48/0.65              = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)))),
% 0.48/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.48/0.65  thf('40', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.48/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.48/0.65  thf('41', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.48/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.48/0.65  thf('42', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.48/0.65      inference('cnf', [status(esa)], [t1_boole])).
% 0.48/0.65  thf('43', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.65      inference('sup+', [status(thm)], ['41', '42'])).
% 0.48/0.65  thf('44', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         (((k2_tarski @ sk_A @ sk_B) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 0.48/0.65          | ~ (r2_hidden @ 
% 0.48/0.65               (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ 
% 0.48/0.65                (k3_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.48/0.65               (k2_tarski @ sk_A @ sk_B))
% 0.48/0.65          | ((k2_tarski @ sk_A @ sk_B) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.48/0.65      inference('demod', [status(thm)], ['39', '40', '43'])).
% 0.48/0.65  thf('45', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         (~ (r2_hidden @ 
% 0.48/0.65             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ 
% 0.48/0.65              (k3_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.48/0.65             (k2_tarski @ sk_A @ sk_B))
% 0.48/0.65          | ((k2_tarski @ sk_A @ sk_B) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.48/0.65      inference('simplify', [status(thm)], ['44'])).
% 0.48/0.65  thf('46', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         (((k2_tarski @ sk_A @ sk_B) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 0.48/0.65          | ((k2_tarski @ sk_A @ sk_B) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.48/0.65      inference('sup-', [status(thm)], ['36', '45'])).
% 0.48/0.65  thf('47', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         ((k2_tarski @ sk_A @ sk_B) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.65      inference('simplify', [status(thm)], ['46'])).
% 0.48/0.65  thf('48', plain,
% 0.48/0.65      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.48/0.65         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.48/0.65          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.48/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.48/0.65  thf('49', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i]:
% 0.48/0.65         (~ (r2_hidden @ X1 @ (k2_tarski @ sk_A @ sk_B))
% 0.48/0.65          | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.65      inference('sup-', [status(thm)], ['47', '48'])).
% 0.48/0.65  thf('50', plain, (![X14 : $i]: (r1_xboole_0 @ X14 @ k1_xboole_0)),
% 0.48/0.65      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.48/0.65  thf('51', plain,
% 0.48/0.65      (![X1 : $i]: ~ (r2_hidden @ X1 @ (k2_tarski @ sk_A @ sk_B))),
% 0.48/0.65      inference('demod', [status(thm)], ['49', '50'])).
% 0.48/0.65  thf('52', plain,
% 0.48/0.65      (![X0 : $i]: ((X0) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0))),
% 0.48/0.65      inference('sup-', [status(thm)], ['6', '51'])).
% 0.48/0.65  thf('53', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.48/0.65      inference('cnf', [status(esa)], [t1_boole])).
% 0.48/0.65  thf('54', plain, (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))),
% 0.48/0.65      inference('sup+', [status(thm)], ['52', '53'])).
% 0.48/0.65  thf(t38_zfmisc_1, axiom,
% 0.48/0.65    (![A:$i,B:$i,C:$i]:
% 0.48/0.65     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.48/0.65       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.48/0.65  thf('55', plain,
% 0.48/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.48/0.65         ((r2_hidden @ X19 @ X20)
% 0.48/0.65          | ~ (r1_tarski @ (k2_tarski @ X19 @ X21) @ X20))),
% 0.48/0.65      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.48/0.65  thf('56', plain,
% 0.48/0.65      (![X0 : $i]: (~ (r1_tarski @ k1_xboole_0 @ X0) | (r2_hidden @ sk_A @ X0))),
% 0.48/0.65      inference('sup-', [status(thm)], ['54', '55'])).
% 0.48/0.65  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.48/0.65  thf('57', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.48/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.48/0.65  thf('58', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 0.48/0.65      inference('demod', [status(thm)], ['56', '57'])).
% 0.48/0.65  thf('59', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         ((k2_tarski @ sk_A @ sk_B) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.65      inference('simplify', [status(thm)], ['46'])).
% 0.48/0.65  thf('60', plain,
% 0.48/0.65      (![X1 : $i]: ~ (r2_hidden @ X1 @ (k2_tarski @ sk_A @ sk_B))),
% 0.48/0.65      inference('demod', [status(thm)], ['49', '50'])).
% 0.48/0.65  thf('61', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i]:
% 0.48/0.65         ~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.65      inference('sup-', [status(thm)], ['59', '60'])).
% 0.48/0.65  thf('62', plain, ($false), inference('sup-', [status(thm)], ['58', '61'])).
% 0.48/0.65  
% 0.48/0.65  % SZS output end Refutation
% 0.48/0.65  
% 0.48/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NY2vqfKKoX

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   98 (1859 expanded)
%              Number of leaves         :   20 ( 528 expanded)
%              Depth                    :   30
%              Number of atoms          :  926 (20433 expanded)
%              Number of equality atoms :   74 (1627 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('9',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('13',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ sk_C )
      | ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = X0 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['17'])).

thf('19',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('20',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = X0 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['17'])).

thf('22',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('23',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ X0 )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = X0 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = X0 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ sk_C )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ k1_xboole_0 ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('27',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('28',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ k1_xboole_0 )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = sk_C )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','29'])).

thf('31',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = sk_C )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = sk_C )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('37',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('38',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ~ ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k2_xboole_0 @ sk_C @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('40',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ~ ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['42'])).

thf('45',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['42'])).

thf('46',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['42'])).

thf('47',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['42'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( sk_C = X0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['18','43','44','45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( sk_C = X0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ X0 ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( sk_C = X0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ X0 )
      | ( sk_C = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['7','51'])).

thf('53',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['42'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('54',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_tarski @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('56',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ X23 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    sk_C != k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['52','59'])).

thf('61',plain,(
    r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ sk_C ),
    inference(condensation,[status(thm)],['60'])).

thf('62',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ ( k2_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ ( k3_tarski @ ( k1_tarski @ sk_C ) ) ),
    inference('sup+',[status(thm)],['2','63'])).

thf('65',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('66',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['42'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('68',plain,
    ( ( k3_tarski @ ( k1_tarski @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['64','68'])).

thf('70',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('71',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ sk_C )
    | ( sk_C
      = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ sk_C ),
    inference(condensation,[status(thm)],['60'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('74',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    sk_C != k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','58'])).

thf('76',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NY2vqfKKoX
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:14:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 157 iterations in 0.074s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(t69_enumset1, axiom,
% 0.20/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.52  thf('0', plain, (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.52  thf(l51_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i]:
% 0.20/0.52         ((k3_tarski @ (k2_tarski @ X16 @ X17)) = (k2_xboole_0 @ X16 @ X17))),
% 0.20/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.52  thf('3', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.52  thf(t12_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i]:
% 0.20/0.52         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.52  thf('5', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.52  thf('7', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf(d3_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.20/0.52       ( ![D:$i]:
% 0.20/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.52           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.20/0.52         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.20/0.52          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.20/0.52          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 0.20/0.52          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.20/0.52  thf(t50_zfmisc_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.52        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X6 @ X4)
% 0.20/0.52          | (r2_hidden @ X6 @ X5)
% 0.20/0.52          | (r2_hidden @ X6 @ X3)
% 0.20/0.52          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.20/0.52         ((r2_hidden @ X6 @ X3)
% 0.20/0.52          | (r2_hidden @ X6 @ X5)
% 0.20/0.52          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.20/0.52          | (r2_hidden @ X0 @ sk_C)
% 0.20/0.52          | (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '13'])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.20/0.52          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X0)
% 0.20/0.52          | ((X1) = (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.20/0.52          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ 
% 0.20/0.52             (k2_tarski @ sk_A @ sk_B))
% 0.20/0.52          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['8', '14'])).
% 0.20/0.52  thf('16', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.20/0.52          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X0)
% 0.20/0.52          | ((X1) = (X0))
% 0.20/0.52          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ 
% 0.20/0.52             (k2_tarski @ sk_A @ sk_B))
% 0.20/0.52          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ sk_C))),
% 0.20/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.20/0.52           sk_C)
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.20/0.52             (k2_tarski @ sk_A @ sk_B))
% 0.20/0.52          | ((k2_tarski @ sk_A @ sk_B) = (X0))
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ X0))),
% 0.20/0.52      inference('eq_fact', [status(thm)], ['17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.20/0.52           sk_C)
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.20/0.52             (k2_tarski @ sk_A @ sk_B))
% 0.20/0.52          | ((k2_tarski @ sk_A @ sk_B) = (X0))
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ X0))),
% 0.20/0.52      inference('eq_fact', [status(thm)], ['17'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.52          | (r2_hidden @ X2 @ X4)
% 0.20/0.52          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.52         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.20/0.52      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.20/0.52           X0)
% 0.20/0.52          | ((k2_tarski @ sk_A @ sk_B) = (X0))
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ sk_C)
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.20/0.52             (k2_xboole_0 @ X1 @ (k2_tarski @ sk_A @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['21', '23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.20/0.52           k1_xboole_0)
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ sk_C)
% 0.20/0.52          | ((k2_tarski @ sk_A @ sk_B) = (X0))
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['20', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.52         sk_C)
% 0.20/0.52        | ((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.20/0.52        | (r2_hidden @ 
% 0.20/0.52           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.52           k1_xboole_0))),
% 0.20/0.52      inference('eq_fact', [status(thm)], ['25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X2 @ X5)
% 0.20/0.52          | (r2_hidden @ X2 @ X4)
% 0.20/0.52          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.52         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 0.20/0.52      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ 
% 0.20/0.52           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.52           k1_xboole_0)
% 0.20/0.52          | ((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.52             (k2_xboole_0 @ sk_C @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.52         k1_xboole_0)
% 0.20/0.52        | ((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.20/0.52        | (r2_hidden @ 
% 0.20/0.52           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.52           k1_xboole_0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['19', '29'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      ((((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.20/0.52        | (r2_hidden @ 
% 0.20/0.52           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.52           k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.52         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.20/0.52      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.52             (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.52  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      ((((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.20/0.52        | (r2_hidden @ 
% 0.20/0.52           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.52           k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.20/0.52         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.20/0.52          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.20/0.52          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      ((((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.20/0.52        | ~ (r2_hidden @ 
% 0.20/0.52             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.52             (k2_tarski @ sk_A @ sk_B))
% 0.20/0.52        | ((k2_tarski @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.52  thf('39', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      ((((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.20/0.52        | ~ (r2_hidden @ 
% 0.20/0.52             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.52             (k2_tarski @ sk_A @ sk_B))
% 0.20/0.52        | ((k2_tarski @ sk_A @ sk_B) = (sk_C)))),
% 0.20/0.52      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      ((~ (r2_hidden @ 
% 0.20/0.52           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.52           (k2_tarski @ sk_A @ sk_B))
% 0.20/0.52        | ((k2_tarski @ sk_A @ sk_B) = (sk_C)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      ((((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.20/0.52        | ((k2_tarski @ sk_A @ sk_B) = (sk_C)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['35', '41'])).
% 0.20/0.52  thf('43', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.20/0.52      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.52  thf('44', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.20/0.52      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.52  thf('45', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.20/0.52      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.53  thf('46', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.20/0.53      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.53  thf('47', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.20/0.53      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ sk_C)
% 0.20/0.53          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ sk_C)
% 0.20/0.53          | ((sk_C) = (X0))
% 0.20/0.53          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['18', '43', '44', '45', '46', '47'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.20/0.53          | ((sk_C) = (X0))
% 0.20/0.53          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ sk_C))),
% 0.20/0.53      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.53         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.20/0.53      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ sk_C)
% 0.20/0.53          | ((sk_C) = (X0))
% 0.20/0.53          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ 
% 0.20/0.53             (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ X0)
% 0.20/0.53          | ((sk_C) = (k1_xboole_0))
% 0.20/0.53          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ sk_C))),
% 0.20/0.53      inference('sup+', [status(thm)], ['7', '51'])).
% 0.20/0.53  thf('53', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.20/0.53      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.53  thf(t41_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k2_tarski @ A @ B ) =
% 0.20/0.53       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         ((k2_tarski @ X11 @ X12)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X12)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.53  thf(t49_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k1_tarski @ X22) @ X23) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ X1 @ (k1_tarski @ X0)) != (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['54', '57'])).
% 0.20/0.53  thf('59', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['53', '58'])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ X0)
% 0.20/0.53          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ sk_C))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['52', '59'])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ sk_C)),
% 0.20/0.53      inference('condensation', [status(thm)], ['60'])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.53         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.20/0.53      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ 
% 0.20/0.53          (k2_xboole_0 @ X0 @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ 
% 0.20/0.53        (k3_tarski @ (k1_tarski @ sk_C)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['2', '63'])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('66', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.20/0.53      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.53  thf('68', plain, (((k3_tarski @ (k1_tarski @ sk_C)) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)),
% 0.20/0.53      inference('demod', [status(thm)], ['64', '68'])).
% 0.20/0.53  thf('70', plain,
% 0.20/0.53      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.20/0.53         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.20/0.53          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.20/0.53          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.20/0.53  thf('71', plain,
% 0.20/0.53      ((~ (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ sk_C)
% 0.20/0.53        | ((sk_C) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.53  thf('72', plain,
% 0.20/0.53      ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ sk_C)),
% 0.20/0.53      inference('condensation', [status(thm)], ['60'])).
% 0.20/0.53  thf('73', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.53  thf('74', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.20/0.53  thf('75', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['53', '58'])).
% 0.20/0.53  thf('76', plain, ($false),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

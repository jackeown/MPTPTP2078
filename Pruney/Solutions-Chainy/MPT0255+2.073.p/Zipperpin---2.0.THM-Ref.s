%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hgIV3wBdGj

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:05 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   98 (1569 expanded)
%              Number of leaves         :   21 ( 436 expanded)
%              Depth                    :   30
%              Number of atoms          :  926 (18707 expanded)
%              Number of equality atoms :   74 (1429 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
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

thf('5',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('9',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ sk_C )
      | ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = X0 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = X0 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('19',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ X0 )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = X0 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = X0 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','20'])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ sk_C )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ k1_xboole_0 ) ),
    inference(eq_fact,[status(thm)],['21'])).

thf('23',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('24',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ k1_xboole_0 )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = sk_C )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','25'])).

thf('27',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = sk_C )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = sk_C )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('33',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('34',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ~ ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k2_xboole_0 @ sk_C @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('36',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('37',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ~ ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C ) ),
    inference(demod,[status(thm)],['34','35','38'])).

thf('40',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['31','40'])).

thf('42',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['41'])).

thf('44',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['41'])).

thf('45',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['41'])).

thf('46',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['41'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( sk_C = X0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['14','42','43','44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( sk_C = X0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ X0 ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( sk_C = X0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ X0 )
      | ( sk_C = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['3','50'])).

thf('52',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['41'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('53',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('55',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ X23 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    sk_C != k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['51','58'])).

thf('60',plain,(
    r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ sk_C ),
    inference(condensation,[status(thm)],['59'])).

thf('61',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('62',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ ( k2_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ ( k3_tarski @ ( k1_tarski @ sk_C ) ) ),
    inference('sup+',[status(thm)],['2','62'])).

thf('64',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf('65',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['41'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('67',plain,
    ( ( k3_tarski @ ( k1_tarski @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['63','67'])).

thf('69',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('70',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ sk_C )
    | ( sk_C
      = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ sk_C ),
    inference(condensation,[status(thm)],['59'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('73',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    sk_C != k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','57'])).

thf('75',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hgIV3wBdGj
% 0.15/0.34  % Computer   : n001.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 17:31:30 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  % Running portfolio for 600 s
% 0.15/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 156 iterations in 0.074s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.35/0.53  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.53  thf(t69_enumset1, axiom,
% 0.35/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.53  thf('0', plain, (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.35/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.53  thf(l51_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.35/0.53  thf('1', plain,
% 0.35/0.53      (![X20 : $i, X21 : $i]:
% 0.35/0.53         ((k3_tarski @ (k2_tarski @ X20 @ X21)) = (k2_xboole_0 @ X20 @ X21))),
% 0.35/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['0', '1'])).
% 0.35/0.53  thf(t1_boole, axiom,
% 0.35/0.53    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.35/0.53  thf('3', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.35/0.53      inference('cnf', [status(esa)], [t1_boole])).
% 0.35/0.53  thf(d3_xboole_0, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.35/0.53       ( ![D:$i]:
% 0.35/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.53           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.35/0.53  thf('4', plain,
% 0.35/0.53      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.35/0.53         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.35/0.53          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.35/0.53          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 0.35/0.53          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.35/0.53  thf(t50_zfmisc_1, conjecture,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.53        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.35/0.53  thf('5', plain,
% 0.35/0.53      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(commutativity_k2_xboole_0, axiom,
% 0.35/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.35/0.53  thf('6', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.35/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['5', '6'])).
% 0.35/0.53  thf('8', plain,
% 0.35/0.53      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X6 @ X4)
% 0.35/0.53          | (r2_hidden @ X6 @ X5)
% 0.35/0.53          | (r2_hidden @ X6 @ X3)
% 0.35/0.53          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.35/0.53  thf('9', plain,
% 0.35/0.53      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.35/0.53         ((r2_hidden @ X6 @ X3)
% 0.35/0.53          | (r2_hidden @ X6 @ X5)
% 0.35/0.53          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 0.35/0.53      inference('simplify', [status(thm)], ['8'])).
% 0.35/0.53  thf('10', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.35/0.53          | (r2_hidden @ X0 @ sk_C)
% 0.35/0.53          | (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['7', '9'])).
% 0.35/0.53  thf('11', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.35/0.53          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X0)
% 0.35/0.53          | ((X1) = (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.35/0.53          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ 
% 0.35/0.53             (k2_tarski @ sk_A @ sk_B))
% 0.35/0.53          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ sk_C))),
% 0.35/0.53      inference('sup-', [status(thm)], ['4', '10'])).
% 0.35/0.53  thf('12', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.35/0.53      inference('cnf', [status(esa)], [t1_boole])).
% 0.35/0.53  thf('13', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.35/0.53          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X0)
% 0.35/0.53          | ((X1) = (X0))
% 0.35/0.53          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ 
% 0.35/0.53             (k2_tarski @ sk_A @ sk_B))
% 0.35/0.53          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ sk_C))),
% 0.35/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.35/0.53  thf('14', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.35/0.53           sk_C)
% 0.35/0.53          | (r2_hidden @ 
% 0.35/0.53             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.35/0.53             (k2_tarski @ sk_A @ sk_B))
% 0.35/0.53          | ((k2_tarski @ sk_A @ sk_B) = (X0))
% 0.35/0.53          | (r2_hidden @ 
% 0.35/0.53             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ X0))),
% 0.35/0.53      inference('eq_fact', [status(thm)], ['13'])).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['5', '6'])).
% 0.35/0.53  thf('16', plain,
% 0.35/0.53      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['5', '6'])).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.35/0.53           sk_C)
% 0.35/0.53          | (r2_hidden @ 
% 0.35/0.53             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.35/0.53             (k2_tarski @ sk_A @ sk_B))
% 0.35/0.53          | ((k2_tarski @ sk_A @ sk_B) = (X0))
% 0.35/0.53          | (r2_hidden @ 
% 0.35/0.53             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ X0))),
% 0.35/0.53      inference('eq_fact', [status(thm)], ['13'])).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X2 @ X3)
% 0.35/0.53          | (r2_hidden @ X2 @ X4)
% 0.35/0.53          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.35/0.53  thf('19', plain,
% 0.35/0.53      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.35/0.53         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.35/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.35/0.53  thf('20', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         ((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.35/0.53           X0)
% 0.35/0.53          | ((k2_tarski @ sk_A @ sk_B) = (X0))
% 0.35/0.53          | (r2_hidden @ 
% 0.35/0.53             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ sk_C)
% 0.35/0.53          | (r2_hidden @ 
% 0.35/0.53             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.35/0.53             (k2_xboole_0 @ X1 @ (k2_tarski @ sk_A @ sk_B))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['17', '19'])).
% 0.35/0.53  thf('21', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.35/0.53           k1_xboole_0)
% 0.35/0.53          | (r2_hidden @ 
% 0.35/0.53             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ sk_C)
% 0.35/0.53          | ((k2_tarski @ sk_A @ sk_B) = (X0))
% 0.35/0.53          | (r2_hidden @ 
% 0.35/0.53             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ X0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['16', '20'])).
% 0.35/0.53  thf('22', plain,
% 0.35/0.53      (((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.35/0.53         sk_C)
% 0.35/0.53        | ((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.35/0.53        | (r2_hidden @ 
% 0.35/0.53           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.35/0.53           k1_xboole_0))),
% 0.35/0.53      inference('eq_fact', [status(thm)], ['21'])).
% 0.35/0.53  thf('23', plain,
% 0.35/0.53      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X2 @ X5)
% 0.35/0.53          | (r2_hidden @ X2 @ X4)
% 0.35/0.53          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.35/0.53  thf('24', plain,
% 0.35/0.53      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.35/0.53         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 0.35/0.53      inference('simplify', [status(thm)], ['23'])).
% 0.35/0.53  thf('25', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((r2_hidden @ 
% 0.35/0.53           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.35/0.53           k1_xboole_0)
% 0.35/0.53          | ((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.35/0.53          | (r2_hidden @ 
% 0.35/0.53             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.35/0.53             (k2_xboole_0 @ sk_C @ X0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['22', '24'])).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      (((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.35/0.53         k1_xboole_0)
% 0.35/0.53        | ((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.35/0.53        | (r2_hidden @ 
% 0.35/0.53           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.35/0.53           k1_xboole_0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['15', '25'])).
% 0.35/0.53  thf('27', plain,
% 0.35/0.53      ((((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.35/0.53        | (r2_hidden @ 
% 0.35/0.53           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.35/0.53           k1_xboole_0))),
% 0.35/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.35/0.53  thf('28', plain,
% 0.35/0.53      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.35/0.53         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.35/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.35/0.53  thf('29', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.35/0.53          | (r2_hidden @ 
% 0.35/0.53             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.38/0.53             (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.38/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.53  thf('30', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.38/0.53      inference('cnf', [status(esa)], [t1_boole])).
% 0.38/0.53  thf('31', plain,
% 0.38/0.53      (![X0 : $i]:
% 0.38/0.53         (((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.38/0.53          | (r2_hidden @ 
% 0.38/0.53             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ X0))),
% 0.38/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.53  thf('32', plain,
% 0.38/0.53      ((((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.38/0.53        | (r2_hidden @ 
% 0.38/0.53           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.38/0.53           k1_xboole_0))),
% 0.38/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.38/0.53  thf('33', plain,
% 0.38/0.53      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.38/0.53         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.38/0.53          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.38/0.53          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.38/0.53      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.38/0.53  thf('34', plain,
% 0.38/0.53      ((((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.38/0.53        | ~ (r2_hidden @ 
% 0.38/0.53             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.38/0.53             (k2_tarski @ sk_A @ sk_B))
% 0.38/0.53        | ((k2_tarski @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ k1_xboole_0)))),
% 0.38/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.53  thf('35', plain,
% 0.38/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.53  thf('36', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.38/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.53  thf(t12_xboole_1, axiom,
% 0.38/0.53    (![A:$i,B:$i]:
% 0.38/0.53     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.38/0.53  thf('37', plain,
% 0.38/0.53      (![X8 : $i, X9 : $i]:
% 0.38/0.53         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.38/0.53      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.53  thf('38', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.53  thf('39', plain,
% 0.38/0.53      ((((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.38/0.53        | ~ (r2_hidden @ 
% 0.38/0.53             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.38/0.53             (k2_tarski @ sk_A @ sk_B))
% 0.38/0.53        | ((k2_tarski @ sk_A @ sk_B) = (sk_C)))),
% 0.38/0.53      inference('demod', [status(thm)], ['34', '35', '38'])).
% 0.38/0.53  thf('40', plain,
% 0.38/0.53      ((~ (r2_hidden @ 
% 0.38/0.53           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.38/0.53           (k2_tarski @ sk_A @ sk_B))
% 0.38/0.53        | ((k2_tarski @ sk_A @ sk_B) = (sk_C)))),
% 0.38/0.53      inference('simplify', [status(thm)], ['39'])).
% 0.38/0.53  thf('41', plain,
% 0.38/0.53      ((((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.38/0.53        | ((k2_tarski @ sk_A @ sk_B) = (sk_C)))),
% 0.38/0.53      inference('sup-', [status(thm)], ['31', '40'])).
% 0.38/0.53  thf('42', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.38/0.53      inference('simplify', [status(thm)], ['41'])).
% 0.38/0.53  thf('43', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.38/0.53      inference('simplify', [status(thm)], ['41'])).
% 0.38/0.53  thf('44', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.38/0.53      inference('simplify', [status(thm)], ['41'])).
% 0.38/0.53  thf('45', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.38/0.53      inference('simplify', [status(thm)], ['41'])).
% 0.38/0.53  thf('46', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.38/0.53      inference('simplify', [status(thm)], ['41'])).
% 0.38/0.53  thf('47', plain,
% 0.38/0.53      (![X0 : $i]:
% 0.38/0.53         ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ sk_C)
% 0.38/0.53          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ sk_C)
% 0.38/0.53          | ((sk_C) = (X0))
% 0.38/0.53          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ X0))),
% 0.38/0.53      inference('demod', [status(thm)], ['14', '42', '43', '44', '45', '46'])).
% 0.38/0.53  thf('48', plain,
% 0.38/0.53      (![X0 : $i]:
% 0.38/0.53         ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.38/0.53          | ((sk_C) = (X0))
% 0.38/0.53          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ sk_C))),
% 0.38/0.53      inference('simplify', [status(thm)], ['47'])).
% 0.38/0.53  thf('49', plain,
% 0.38/0.53      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.38/0.53         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.38/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.38/0.53  thf('50', plain,
% 0.38/0.53      (![X0 : $i, X1 : $i]:
% 0.38/0.53         ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ sk_C)
% 0.38/0.53          | ((sk_C) = (X0))
% 0.38/0.53          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ 
% 0.38/0.53             (k2_xboole_0 @ X1 @ X0)))),
% 0.38/0.53      inference('sup-', [status(thm)], ['48', '49'])).
% 0.38/0.53  thf('51', plain,
% 0.38/0.53      (![X0 : $i]:
% 0.38/0.53         ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ X0)
% 0.38/0.53          | ((sk_C) = (k1_xboole_0))
% 0.38/0.53          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ sk_C))),
% 0.38/0.53      inference('sup+', [status(thm)], ['3', '50'])).
% 0.38/0.53  thf('52', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.38/0.53      inference('simplify', [status(thm)], ['41'])).
% 0.38/0.53  thf(t41_enumset1, axiom,
% 0.38/0.53    (![A:$i,B:$i]:
% 0.38/0.53     ( ( k2_tarski @ A @ B ) =
% 0.38/0.53       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.38/0.53  thf('53', plain,
% 0.38/0.53      (![X12 : $i, X13 : $i]:
% 0.38/0.53         ((k2_tarski @ X12 @ X13)
% 0.38/0.53           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13)))),
% 0.38/0.53      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.38/0.53  thf('54', plain,
% 0.38/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.53  thf(t49_zfmisc_1, axiom,
% 0.38/0.53    (![A:$i,B:$i]:
% 0.38/0.53     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.38/0.53  thf('55', plain,
% 0.38/0.53      (![X22 : $i, X23 : $i]:
% 0.38/0.53         ((k2_xboole_0 @ (k1_tarski @ X22) @ X23) != (k1_xboole_0))),
% 0.38/0.53      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.38/0.53  thf('56', plain,
% 0.38/0.53      (![X0 : $i, X1 : $i]:
% 0.38/0.53         ((k2_xboole_0 @ X1 @ (k1_tarski @ X0)) != (k1_xboole_0))),
% 0.38/0.53      inference('sup-', [status(thm)], ['54', '55'])).
% 0.38/0.53  thf('57', plain,
% 0.38/0.53      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 0.38/0.53      inference('sup-', [status(thm)], ['53', '56'])).
% 0.38/0.53  thf('58', plain, (((sk_C) != (k1_xboole_0))),
% 0.38/0.53      inference('sup-', [status(thm)], ['52', '57'])).
% 0.38/0.53  thf('59', plain,
% 0.38/0.53      (![X0 : $i]:
% 0.38/0.53         ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ X0)
% 0.38/0.53          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ sk_C))),
% 0.38/0.53      inference('simplify_reflect-', [status(thm)], ['51', '58'])).
% 0.38/0.53  thf('60', plain,
% 0.38/0.53      ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ sk_C)),
% 0.38/0.53      inference('condensation', [status(thm)], ['59'])).
% 0.38/0.53  thf('61', plain,
% 0.38/0.53      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.38/0.53         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.38/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.38/0.53  thf('62', plain,
% 0.38/0.53      (![X0 : $i]:
% 0.38/0.53         (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ 
% 0.38/0.53          (k2_xboole_0 @ X0 @ sk_C))),
% 0.38/0.53      inference('sup-', [status(thm)], ['60', '61'])).
% 0.38/0.53  thf('63', plain,
% 0.38/0.53      ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ 
% 0.38/0.53        (k3_tarski @ (k1_tarski @ sk_C)))),
% 0.38/0.53      inference('sup+', [status(thm)], ['2', '62'])).
% 0.38/0.53  thf('64', plain,
% 0.38/0.53      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.38/0.53      inference('demod', [status(thm)], ['5', '6'])).
% 0.38/0.53  thf('65', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.38/0.53      inference('simplify', [status(thm)], ['41'])).
% 0.38/0.53  thf('66', plain,
% 0.38/0.53      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.38/0.53      inference('sup+', [status(thm)], ['0', '1'])).
% 0.38/0.53  thf('67', plain, (((k3_tarski @ (k1_tarski @ sk_C)) = (k1_xboole_0))),
% 0.38/0.53      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.38/0.53  thf('68', plain,
% 0.38/0.53      ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)),
% 0.38/0.53      inference('demod', [status(thm)], ['63', '67'])).
% 0.38/0.53  thf('69', plain,
% 0.38/0.53      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.38/0.53         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.38/0.53          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.38/0.53          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.38/0.53      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.38/0.53  thf('70', plain,
% 0.38/0.53      ((~ (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ sk_C)
% 0.38/0.53        | ((sk_C) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.38/0.53      inference('sup-', [status(thm)], ['68', '69'])).
% 0.38/0.53  thf('71', plain,
% 0.38/0.53      ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ sk_C)),
% 0.38/0.53      inference('condensation', [status(thm)], ['59'])).
% 0.38/0.53  thf('72', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.53  thf('73', plain, (((sk_C) = (k1_xboole_0))),
% 0.38/0.53      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.38/0.53  thf('74', plain, (((sk_C) != (k1_xboole_0))),
% 0.38/0.53      inference('sup-', [status(thm)], ['52', '57'])).
% 0.38/0.53  thf('75', plain, ($false),
% 0.38/0.53      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 0.38/0.53  
% 0.38/0.53  % SZS output end Refutation
% 0.38/0.53  
% 0.38/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

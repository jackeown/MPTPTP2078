%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4YNzTbaDZ1

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 (1556 expanded)
%              Number of leaves         :   15 ( 430 expanded)
%              Depth                    :   29
%              Number of atoms          :  866 (18659 expanded)
%              Number of equality atoms :   68 (1449 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('4',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('6',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('8',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ sk_C )
      | ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = X0 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('15',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ X0 )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = X0 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = X0 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ sk_C )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ k1_xboole_0 ) ),
    inference(eq_fact,[status(thm)],['17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('20',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ k1_xboole_0 )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = sk_C )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','21'])).

thf('23',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = sk_C )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_B )
        = sk_C )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('29',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('30',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ~ ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k2_xboole_0 @ sk_C @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ~ ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C ) ),
    inference(demod,[status(thm)],['30','31','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','38'])).

thf('40',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = X0 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('42',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['37'])).

thf('43',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['37'])).

thf('44',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['37'])).

thf('45',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['37'])).

thf('46',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['37'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( sk_C = X0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45','46'])).

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
    inference(simplify,[status(thm)],['14'])).

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
    inference('sup+',[status(thm)],['40','50'])).

thf('52',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['37'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('53',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X11 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ X21 )
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
    inference(simplify,[status(thm)],['14'])).

thf('62',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ ( k2_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['39','62'])).

thf('64',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('65',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ sk_C )
    | ( sk_C
      = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ sk_C ),
    inference(condensation,[status(thm)],['59'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('68',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    sk_C != k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','57'])).

thf('70',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4YNzTbaDZ1
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:18:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 158 iterations in 0.091s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.54  thf(t50_zfmisc_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.54        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.54  thf(d3_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.20/0.54       ( ![D:$i]:
% 0.20/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.54           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.20/0.54         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.20/0.54          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.20/0.54          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 0.20/0.54          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X6 @ X4)
% 0.20/0.54          | (r2_hidden @ X6 @ X5)
% 0.20/0.54          | (r2_hidden @ X6 @ X3)
% 0.20/0.54          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         ((r2_hidden @ X6 @ X3)
% 0.20/0.54          | (r2_hidden @ X6 @ X5)
% 0.20/0.54          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.20/0.54          | (r2_hidden @ X0 @ sk_C)
% 0.20/0.54          | (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['6', '8'])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.20/0.54          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X0)
% 0.20/0.54          | ((X1) = (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.20/0.54          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ 
% 0.20/0.54             (k2_tarski @ sk_A @ sk_B))
% 0.20/0.54          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ sk_C))),
% 0.20/0.54      inference('sup-', [status(thm)], ['5', '9'])).
% 0.20/0.54  thf(t1_boole, axiom,
% 0.20/0.54    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.54  thf('11', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.20/0.54          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X0)
% 0.20/0.54          | ((X1) = (X0))
% 0.20/0.54          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ 
% 0.20/0.54             (k2_tarski @ sk_A @ sk_B))
% 0.20/0.54          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ sk_C))),
% 0.20/0.54      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.20/0.54           sk_C)
% 0.20/0.54          | (r2_hidden @ 
% 0.20/0.54             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.20/0.54             (k2_tarski @ sk_A @ sk_B))
% 0.20/0.54          | ((k2_tarski @ sk_A @ sk_B) = (X0))
% 0.20/0.54          | (r2_hidden @ 
% 0.20/0.54             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ X0))),
% 0.20/0.54      inference('eq_fact', [status(thm)], ['12'])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.54          | (r2_hidden @ X2 @ X4)
% 0.20/0.54          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.54         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.20/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.20/0.54           X0)
% 0.20/0.54          | ((k2_tarski @ sk_A @ sk_B) = (X0))
% 0.20/0.54          | (r2_hidden @ 
% 0.20/0.54             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ sk_C)
% 0.20/0.54          | (r2_hidden @ 
% 0.20/0.54             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.20/0.54             (k2_xboole_0 @ X1 @ (k2_tarski @ sk_A @ sk_B))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['13', '15'])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.20/0.54           k1_xboole_0)
% 0.20/0.54          | (r2_hidden @ 
% 0.20/0.54             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ sk_C)
% 0.20/0.54          | ((k2_tarski @ sk_A @ sk_B) = (X0))
% 0.20/0.54          | (r2_hidden @ 
% 0.20/0.54             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['4', '16'])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.54         sk_C)
% 0.20/0.54        | ((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.20/0.54        | (r2_hidden @ 
% 0.20/0.54           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.54           k1_xboole_0))),
% 0.20/0.54      inference('eq_fact', [status(thm)], ['17'])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X2 @ X5)
% 0.20/0.54          | (r2_hidden @ X2 @ X4)
% 0.20/0.54          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.54         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 0.20/0.54      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ 
% 0.20/0.54           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.54           k1_xboole_0)
% 0.20/0.54          | ((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.20/0.54          | (r2_hidden @ 
% 0.20/0.54             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.54             (k2_xboole_0 @ sk_C @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['18', '20'])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.54         k1_xboole_0)
% 0.20/0.54        | ((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.20/0.54        | (r2_hidden @ 
% 0.20/0.54           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.54           k1_xboole_0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['3', '21'])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      ((((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.20/0.54        | (r2_hidden @ 
% 0.20/0.54           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.54           k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.54         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.20/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.20/0.54          | (r2_hidden @ 
% 0.20/0.54             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.54             (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.54  thf('26', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.20/0.54          | (r2_hidden @ 
% 0.20/0.54             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      ((((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.20/0.54        | (r2_hidden @ 
% 0.20/0.54           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.54           k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.20/0.54         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.20/0.54          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.20/0.54          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      ((((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.20/0.54        | ~ (r2_hidden @ 
% 0.20/0.54             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.54             (k2_tarski @ sk_A @ sk_B))
% 0.20/0.54        | ((k2_tarski @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.54  thf('33', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.54  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      ((((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.20/0.54        | ~ (r2_hidden @ 
% 0.20/0.54             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.54             (k2_tarski @ sk_A @ sk_B))
% 0.20/0.54        | ((k2_tarski @ sk_A @ sk_B) = (sk_C)))),
% 0.20/0.54      inference('demod', [status(thm)], ['30', '31', '34'])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      ((~ (r2_hidden @ 
% 0.20/0.54           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.20/0.54           (k2_tarski @ sk_A @ sk_B))
% 0.20/0.54        | ((k2_tarski @ sk_A @ sk_B) = (sk_C)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      ((((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.20/0.54        | ((k2_tarski @ sk_A @ sk_B) = (sk_C)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['27', '36'])).
% 0.20/0.54  thf('38', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.20/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.54  thf('39', plain, (((k2_xboole_0 @ sk_C @ sk_C) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['2', '38'])).
% 0.20/0.54  thf('40', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.20/0.54           sk_C)
% 0.20/0.54          | (r2_hidden @ 
% 0.20/0.54             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.20/0.54             (k2_tarski @ sk_A @ sk_B))
% 0.20/0.54          | ((k2_tarski @ sk_A @ sk_B) = (X0))
% 0.20/0.54          | (r2_hidden @ 
% 0.20/0.54             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ X0))),
% 0.20/0.54      inference('eq_fact', [status(thm)], ['12'])).
% 0.20/0.54  thf('42', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.20/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.54  thf('43', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.20/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.54  thf('44', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.20/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.54  thf('45', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.20/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.54  thf('46', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.20/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ sk_C)
% 0.20/0.54          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ sk_C)
% 0.20/0.54          | ((sk_C) = (X0))
% 0.20/0.54          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['41', '42', '43', '44', '45', '46'])).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.20/0.54          | ((sk_C) = (X0))
% 0.20/0.54          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ sk_C))),
% 0.20/0.54      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.54         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.20/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.54  thf('50', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ sk_C)
% 0.20/0.54          | ((sk_C) = (X0))
% 0.20/0.54          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ 
% 0.20/0.54             (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ X0)
% 0.20/0.54          | ((sk_C) = (k1_xboole_0))
% 0.20/0.54          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ sk_C))),
% 0.20/0.54      inference('sup+', [status(thm)], ['40', '50'])).
% 0.20/0.54  thf('52', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.20/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.54  thf(t41_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k2_tarski @ A @ B ) =
% 0.20/0.54       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (![X10 : $i, X11 : $i]:
% 0.20/0.54         ((k2_tarski @ X10 @ X11)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_tarski @ X11)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.54  thf('54', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.54  thf(t49_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      (![X20 : $i, X21 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k1_tarski @ X20) @ X21) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.54  thf('56', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ X1 @ (k1_tarski @ X0)) != (k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.54  thf('57', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['53', '56'])).
% 0.20/0.54  thf('58', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['52', '57'])).
% 0.20/0.54  thf('59', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ X0)
% 0.20/0.54          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ sk_C))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['51', '58'])).
% 0.20/0.54  thf('60', plain,
% 0.20/0.54      ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ sk_C)),
% 0.20/0.54      inference('condensation', [status(thm)], ['59'])).
% 0.20/0.54  thf('61', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.54         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.20/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.54  thf('62', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ 
% 0.20/0.54          (k2_xboole_0 @ X0 @ sk_C))),
% 0.20/0.54      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.54  thf('63', plain,
% 0.20/0.54      ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)),
% 0.20/0.54      inference('sup+', [status(thm)], ['39', '62'])).
% 0.20/0.55  thf('64', plain,
% 0.20/0.55      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.20/0.55         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.20/0.55          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.20/0.55          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.20/0.55  thf('65', plain,
% 0.20/0.55      ((~ (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ sk_C)
% 0.20/0.55        | ((sk_C) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.55  thf('66', plain,
% 0.20/0.55      ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ sk_C)),
% 0.20/0.55      inference('condensation', [status(thm)], ['59'])).
% 0.20/0.55  thf('67', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.55  thf('68', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.20/0.55  thf('69', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['52', '57'])).
% 0.20/0.55  thf('70', plain, ($false),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

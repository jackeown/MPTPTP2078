%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xph9UsbL0X

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:06 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   90 (1847 expanded)
%              Number of leaves         :   17 ( 523 expanded)
%              Depth                    :   29
%              Number of atoms          :  876 (20355 expanded)
%              Number of equality atoms :   68 (1617 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('11',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = X0 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['16'])).

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
    inference('sup+',[status(thm)],['4','20'])).

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
    inference('sup+',[status(thm)],['3','25'])).

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
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

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
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('36',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ~ ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = X0 )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['16'])).

thf('43',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['38'])).

thf('44',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['38'])).

thf('45',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['38'])).

thf('46',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['38'])).

thf('47',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['38'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ X0 ) @ sk_C )
      | ( sk_C = X0 )
      | ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43','44','45','46','47'])).

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
    inference(simplify,[status(thm)],['18'])).

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
    inference('sup+',[status(thm)],['41','51'])).

thf('53',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = sk_C ),
    inference(simplify,[status(thm)],['38'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('54',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_tarski @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_tarski @ X14 ) ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ X26 )
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
    inference(simplify,[status(thm)],['18'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ ( k2_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['40','63'])).

thf('65',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('66',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ sk_C )
    | ( sk_C
      = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r2_hidden @ ( sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ sk_C ),
    inference(condensation,[status(thm)],['60'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('69',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    sk_C != k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','58'])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xph9UsbL0X
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:23:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 156 iterations in 0.153s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.41/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.60  thf(t50_zfmisc_1, conjecture,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.60        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.41/0.60  thf('0', plain,
% 0.41/0.60      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(commutativity_k2_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.41/0.60      inference('demod', [status(thm)], ['0', '1'])).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.41/0.60      inference('demod', [status(thm)], ['0', '1'])).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.41/0.60      inference('demod', [status(thm)], ['0', '1'])).
% 0.41/0.60  thf(d3_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.41/0.60       ( ![D:$i]:
% 0.41/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.41/0.60           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.41/0.60         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.41/0.60          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.41/0.60          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 0.41/0.60          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.41/0.60  thf('6', plain,
% 0.41/0.60      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.41/0.60      inference('demod', [status(thm)], ['0', '1'])).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X6 @ X4)
% 0.41/0.60          | (r2_hidden @ X6 @ X5)
% 0.41/0.60          | (r2_hidden @ X6 @ X3)
% 0.41/0.60          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.41/0.60         ((r2_hidden @ X6 @ X3)
% 0.41/0.60          | (r2_hidden @ X6 @ X5)
% 0.41/0.60          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['7'])).
% 0.41/0.60  thf('9', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.41/0.60          | (r2_hidden @ X0 @ sk_C)
% 0.41/0.60          | (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['6', '8'])).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.41/0.60          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X0)
% 0.41/0.60          | ((X1) = (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.41/0.60          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ 
% 0.41/0.60             (k2_tarski @ sk_A @ sk_B))
% 0.41/0.60          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ sk_C))),
% 0.41/0.60      inference('sup-', [status(thm)], ['5', '9'])).
% 0.41/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.41/0.60  thf('11', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.41/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.60  thf(t12_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      (![X8 : $i, X9 : $i]:
% 0.41/0.60         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.41/0.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.41/0.60  thf('13', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf('14', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.41/0.60  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.41/0.60          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X0)
% 0.41/0.60          | ((X1) = (X0))
% 0.41/0.60          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ 
% 0.41/0.60             (k2_tarski @ sk_A @ sk_B))
% 0.41/0.60          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ sk_C))),
% 0.41/0.60      inference('demod', [status(thm)], ['10', '15'])).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.41/0.60           sk_C)
% 0.41/0.60          | (r2_hidden @ 
% 0.41/0.60             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.41/0.60             (k2_tarski @ sk_A @ sk_B))
% 0.41/0.60          | ((k2_tarski @ sk_A @ sk_B) = (X0))
% 0.41/0.60          | (r2_hidden @ 
% 0.41/0.60             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ X0))),
% 0.41/0.60      inference('eq_fact', [status(thm)], ['16'])).
% 0.41/0.60  thf('18', plain,
% 0.41/0.60      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X2 @ X3)
% 0.41/0.60          | (r2_hidden @ X2 @ X4)
% 0.41/0.60          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.41/0.60         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.41/0.60      inference('simplify', [status(thm)], ['18'])).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.41/0.60           X0)
% 0.41/0.60          | ((k2_tarski @ sk_A @ sk_B) = (X0))
% 0.41/0.60          | (r2_hidden @ 
% 0.41/0.60             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ sk_C)
% 0.41/0.60          | (r2_hidden @ 
% 0.41/0.60             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.41/0.60             (k2_xboole_0 @ X1 @ (k2_tarski @ sk_A @ sk_B))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['17', '19'])).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.41/0.60           k1_xboole_0)
% 0.41/0.60          | (r2_hidden @ 
% 0.41/0.60             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ sk_C)
% 0.41/0.60          | ((k2_tarski @ sk_A @ sk_B) = (X0))
% 0.41/0.60          | (r2_hidden @ 
% 0.41/0.60             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['4', '20'])).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      (((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.41/0.60         sk_C)
% 0.41/0.60        | ((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.41/0.60        | (r2_hidden @ 
% 0.41/0.60           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.41/0.60           k1_xboole_0))),
% 0.41/0.60      inference('eq_fact', [status(thm)], ['21'])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X2 @ X5)
% 0.41/0.60          | (r2_hidden @ X2 @ X4)
% 0.41/0.60          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.41/0.60  thf('24', plain,
% 0.41/0.60      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.41/0.60         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 0.41/0.60      inference('simplify', [status(thm)], ['23'])).
% 0.41/0.60  thf('25', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((r2_hidden @ 
% 0.41/0.60           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.41/0.60           k1_xboole_0)
% 0.41/0.60          | ((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.41/0.60          | (r2_hidden @ 
% 0.41/0.60             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.41/0.60             (k2_xboole_0 @ sk_C @ X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['22', '24'])).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      (((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.41/0.60         k1_xboole_0)
% 0.41/0.60        | ((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.41/0.60        | (r2_hidden @ 
% 0.41/0.60           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.41/0.60           k1_xboole_0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['3', '25'])).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      ((((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.41/0.60        | (r2_hidden @ 
% 0.41/0.60           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.41/0.60           k1_xboole_0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['26'])).
% 0.41/0.60  thf('28', plain,
% 0.41/0.60      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.41/0.60         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.41/0.60      inference('simplify', [status(thm)], ['18'])).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.41/0.60          | (r2_hidden @ 
% 0.41/0.60             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.41/0.60             (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.41/0.60  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.60  thf('31', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.41/0.60          | (r2_hidden @ 
% 0.41/0.60             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['29', '30'])).
% 0.41/0.60  thf('32', plain,
% 0.41/0.60      ((((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.41/0.60        | (r2_hidden @ 
% 0.41/0.60           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.41/0.60           k1_xboole_0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['26'])).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.41/0.60         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.41/0.60          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.41/0.60          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      ((((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.41/0.60        | ~ (r2_hidden @ 
% 0.41/0.60             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.41/0.60             (k2_tarski @ sk_A @ sk_B))
% 0.41/0.60        | ((k2_tarski @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['32', '33'])).
% 0.41/0.60  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      ((((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.41/0.60        | ~ (r2_hidden @ 
% 0.41/0.60             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.41/0.60             (k2_tarski @ sk_A @ sk_B))
% 0.41/0.60        | ((k2_tarski @ sk_A @ sk_B) = (sk_C)))),
% 0.41/0.60      inference('demod', [status(thm)], ['34', '35'])).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      ((~ (r2_hidden @ 
% 0.41/0.60           (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ sk_C) @ 
% 0.41/0.60           (k2_tarski @ sk_A @ sk_B))
% 0.41/0.60        | ((k2_tarski @ sk_A @ sk_B) = (sk_C)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['36'])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      ((((k2_tarski @ sk_A @ sk_B) = (sk_C))
% 0.41/0.60        | ((k2_tarski @ sk_A @ sk_B) = (sk_C)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['31', '37'])).
% 0.41/0.60  thf('39', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.41/0.60      inference('simplify', [status(thm)], ['38'])).
% 0.41/0.60  thf('40', plain, (((k2_xboole_0 @ sk_C @ sk_C) = (k1_xboole_0))),
% 0.41/0.60      inference('demod', [status(thm)], ['2', '39'])).
% 0.41/0.60  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.60  thf('42', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((r2_hidden @ (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.41/0.60           sk_C)
% 0.41/0.60          | (r2_hidden @ 
% 0.41/0.60             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ 
% 0.41/0.60             (k2_tarski @ sk_A @ sk_B))
% 0.41/0.60          | ((k2_tarski @ sk_A @ sk_B) = (X0))
% 0.41/0.60          | (r2_hidden @ 
% 0.41/0.60             (sk_D @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0 @ X0) @ X0))),
% 0.41/0.60      inference('eq_fact', [status(thm)], ['16'])).
% 0.41/0.60  thf('43', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.41/0.60      inference('simplify', [status(thm)], ['38'])).
% 0.41/0.60  thf('44', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.41/0.60      inference('simplify', [status(thm)], ['38'])).
% 0.41/0.60  thf('45', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.41/0.60      inference('simplify', [status(thm)], ['38'])).
% 0.41/0.60  thf('46', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.41/0.60      inference('simplify', [status(thm)], ['38'])).
% 0.41/0.60  thf('47', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.41/0.60      inference('simplify', [status(thm)], ['38'])).
% 0.41/0.60  thf('48', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ sk_C)
% 0.41/0.60          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ sk_C)
% 0.41/0.60          | ((sk_C) = (X0))
% 0.41/0.60          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['42', '43', '44', '45', '46', '47'])).
% 0.41/0.60  thf('49', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.41/0.60          | ((sk_C) = (X0))
% 0.41/0.60          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ sk_C))),
% 0.41/0.60      inference('simplify', [status(thm)], ['48'])).
% 0.41/0.60  thf('50', plain,
% 0.41/0.60      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.41/0.60         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.41/0.60      inference('simplify', [status(thm)], ['18'])).
% 0.41/0.60  thf('51', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ sk_C)
% 0.41/0.60          | ((sk_C) = (X0))
% 0.41/0.60          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ X0) @ 
% 0.41/0.60             (k2_xboole_0 @ X1 @ X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['49', '50'])).
% 0.41/0.60  thf('52', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ X0)
% 0.41/0.60          | ((sk_C) = (k1_xboole_0))
% 0.41/0.60          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ sk_C))),
% 0.41/0.60      inference('sup+', [status(thm)], ['41', '51'])).
% 0.41/0.60  thf('53', plain, (((k2_tarski @ sk_A @ sk_B) = (sk_C))),
% 0.41/0.60      inference('simplify', [status(thm)], ['38'])).
% 0.41/0.60  thf(t41_enumset1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( k2_tarski @ A @ B ) =
% 0.41/0.60       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.41/0.60  thf('54', plain,
% 0.41/0.60      (![X13 : $i, X14 : $i]:
% 0.41/0.60         ((k2_tarski @ X13 @ X14)
% 0.41/0.60           = (k2_xboole_0 @ (k1_tarski @ X13) @ (k1_tarski @ X14)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.41/0.60  thf('55', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.41/0.60  thf(t49_zfmisc_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.41/0.60  thf('56', plain,
% 0.41/0.60      (![X25 : $i, X26 : $i]:
% 0.41/0.60         ((k2_xboole_0 @ (k1_tarski @ X25) @ X26) != (k1_xboole_0))),
% 0.41/0.60      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.41/0.60  thf('57', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k2_xboole_0 @ X1 @ (k1_tarski @ X0)) != (k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['55', '56'])).
% 0.41/0.60  thf('58', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['54', '57'])).
% 0.41/0.60  thf('59', plain, (((sk_C) != (k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['53', '58'])).
% 0.41/0.60  thf('60', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ X0)
% 0.41/0.60          | (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ sk_C))),
% 0.41/0.60      inference('simplify_reflect-', [status(thm)], ['52', '59'])).
% 0.41/0.60  thf('61', plain,
% 0.41/0.60      ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ sk_C)),
% 0.41/0.60      inference('condensation', [status(thm)], ['60'])).
% 0.41/0.60  thf('62', plain,
% 0.41/0.60      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.41/0.60         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.41/0.60      inference('simplify', [status(thm)], ['18'])).
% 0.41/0.60  thf('63', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ 
% 0.41/0.60          (k2_xboole_0 @ X0 @ sk_C))),
% 0.41/0.60      inference('sup-', [status(thm)], ['61', '62'])).
% 0.41/0.60  thf('64', plain,
% 0.41/0.60      ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)),
% 0.41/0.60      inference('sup+', [status(thm)], ['40', '63'])).
% 0.41/0.60  thf('65', plain,
% 0.41/0.60      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.41/0.60         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.41/0.60          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.41/0.60          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.41/0.60  thf('66', plain,
% 0.41/0.60      ((~ (r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ sk_C)
% 0.41/0.60        | ((sk_C) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['64', '65'])).
% 0.41/0.60  thf('67', plain,
% 0.41/0.60      ((r2_hidden @ (sk_D @ sk_C @ k1_xboole_0 @ k1_xboole_0) @ sk_C)),
% 0.41/0.60      inference('condensation', [status(thm)], ['60'])).
% 0.41/0.60  thf('68', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf('69', plain, (((sk_C) = (k1_xboole_0))),
% 0.41/0.60      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.41/0.60  thf('70', plain, (((sk_C) != (k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['53', '58'])).
% 0.41/0.60  thf('71', plain, ($false),
% 0.41/0.60      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

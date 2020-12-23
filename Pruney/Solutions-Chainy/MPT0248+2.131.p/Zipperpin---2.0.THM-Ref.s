%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pJd0nKRWYC

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:37 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 292 expanded)
%              Number of leaves         :   22 (  82 expanded)
%              Depth                    :   19
%              Number of atoms          :  724 (3807 expanded)
%              Number of equality atoms :  109 ( 802 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_C_2
     != ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X50: $i,X51: $i] :
      ( ( X51
        = ( k1_tarski @ X50 ) )
      | ( X51 = k1_xboole_0 )
      | ~ ( r1_tarski @ X51 @ ( k1_tarski @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( sk_B
     != ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','6','22'])).

thf('24',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X12: $i] :
      ( ( r1_xboole_0 @ X12 @ X12 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('26',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['25'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('29',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('37',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X48 ) @ X49 )
      | ( r2_hidden @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('38',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('39',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( r1_xboole_0 @ X14 @ X17 )
      | ~ ( r1_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_C_2 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('42',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('43',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('47',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( r2_hidden @ X55 @ X56 )
      | ~ ( r1_tarski @ ( k2_tarski @ X55 @ X57 ) @ X56 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','48'])).

thf('50',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['41','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','52'])).

thf('54',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_C_2 @ sk_B )
    | ( r1_tarski @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,
    ( ( sk_C_2
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('63',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('67',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('70',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['68','69'])).

thf('71',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['62','70'])).

thf('72',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('73',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['61','71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['35','73'])).

thf('75',plain,(
    sk_C_2 != sk_C_2 ),
    inference(demod,[status(thm)],['24','74'])).

thf('76',plain,(
    $false ),
    inference(simplify,[status(thm)],['75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pJd0nKRWYC
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.02/1.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.02/1.23  % Solved by: fo/fo7.sh
% 1.02/1.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.02/1.23  % done 2021 iterations in 0.778s
% 1.02/1.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.02/1.23  % SZS output start Refutation
% 1.02/1.23  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.02/1.23  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.02/1.23  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.02/1.23  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.02/1.23  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.02/1.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.02/1.23  thf(sk_B_type, type, sk_B: $i).
% 1.02/1.23  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.02/1.23  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.02/1.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.02/1.23  thf(sk_A_type, type, sk_A: $i).
% 1.02/1.23  thf(t43_zfmisc_1, conjecture,
% 1.02/1.23    (![A:$i,B:$i,C:$i]:
% 1.02/1.23     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.02/1.23          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.02/1.23          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.05/1.23          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.05/1.23  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.23    (~( ![A:$i,B:$i,C:$i]:
% 1.05/1.23        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.05/1.23             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.05/1.23             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.05/1.23             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 1.05/1.23    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 1.05/1.23  thf('0', plain,
% 1.05/1.23      ((((sk_B) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('1', plain,
% 1.05/1.23      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 1.05/1.23         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 1.05/1.23      inference('split', [status(esa)], ['0'])).
% 1.05/1.23  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('3', plain,
% 1.05/1.23      ((((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 1.05/1.23         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 1.05/1.23      inference('demod', [status(thm)], ['1', '2'])).
% 1.05/1.23  thf('4', plain,
% 1.05/1.23      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 1.05/1.23      inference('split', [status(esa)], ['0'])).
% 1.05/1.23  thf('5', plain,
% 1.05/1.23      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('6', plain,
% 1.05/1.23      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 1.05/1.23      inference('split', [status(esa)], ['5'])).
% 1.05/1.23  thf(t7_xboole_1, axiom,
% 1.05/1.23    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.05/1.23  thf('7', plain,
% 1.05/1.23      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 1.05/1.23      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.05/1.23  thf('8', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf(l3_zfmisc_1, axiom,
% 1.05/1.23    (![A:$i,B:$i]:
% 1.05/1.23     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.05/1.23       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.05/1.23  thf('9', plain,
% 1.05/1.23      (![X50 : $i, X51 : $i]:
% 1.05/1.23         (((X51) = (k1_tarski @ X50))
% 1.05/1.23          | ((X51) = (k1_xboole_0))
% 1.05/1.23          | ~ (r1_tarski @ X51 @ (k1_tarski @ X50)))),
% 1.05/1.23      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.05/1.23  thf('10', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 1.05/1.23          | ((X0) = (k1_xboole_0))
% 1.05/1.23          | ((X0) = (k1_tarski @ sk_A)))),
% 1.05/1.23      inference('sup-', [status(thm)], ['8', '9'])).
% 1.05/1.23  thf('11', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('12', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 1.05/1.23          | ((X0) = (k1_xboole_0))
% 1.05/1.23          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 1.05/1.23      inference('demod', [status(thm)], ['10', '11'])).
% 1.05/1.23  thf('13', plain,
% 1.05/1.23      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.23      inference('sup-', [status(thm)], ['7', '12'])).
% 1.05/1.23  thf('14', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('15', plain,
% 1.05/1.23      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('16', plain,
% 1.05/1.23      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.05/1.23      inference('split', [status(esa)], ['15'])).
% 1.05/1.23  thf('17', plain,
% 1.05/1.23      ((((sk_B) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 1.05/1.23         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['14', '16'])).
% 1.05/1.23  thf('18', plain,
% 1.05/1.23      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 1.05/1.23         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['13', '17'])).
% 1.05/1.23  thf('19', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.05/1.23      inference('simplify', [status(thm)], ['18'])).
% 1.05/1.23  thf('20', plain,
% 1.05/1.23      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('split', [status(esa)], ['0'])).
% 1.05/1.23  thf('21', plain,
% 1.05/1.23      ((((sk_B) != (sk_B)))
% 1.05/1.23         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['19', '20'])).
% 1.05/1.23  thf('22', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 1.05/1.23      inference('simplify', [status(thm)], ['21'])).
% 1.05/1.23  thf('23', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 1.05/1.23      inference('sat_resolution*', [status(thm)], ['4', '6', '22'])).
% 1.05/1.23  thf('24', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.05/1.23      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 1.05/1.23  thf(t66_xboole_1, axiom,
% 1.05/1.23    (![A:$i]:
% 1.05/1.23     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 1.05/1.23       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.05/1.23  thf('25', plain,
% 1.05/1.23      (![X12 : $i]: ((r1_xboole_0 @ X12 @ X12) | ((X12) != (k1_xboole_0)))),
% 1.05/1.23      inference('cnf', [status(esa)], [t66_xboole_1])).
% 1.05/1.23  thf('26', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 1.05/1.23      inference('simplify', [status(thm)], ['25'])).
% 1.05/1.23  thf(d3_tarski, axiom,
% 1.05/1.23    (![A:$i,B:$i]:
% 1.05/1.23     ( ( r1_tarski @ A @ B ) <=>
% 1.05/1.23       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.05/1.23  thf('27', plain,
% 1.05/1.23      (![X1 : $i, X3 : $i]:
% 1.05/1.23         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.05/1.23      inference('cnf', [status(esa)], [d3_tarski])).
% 1.05/1.23  thf('28', plain,
% 1.05/1.23      (![X1 : $i, X3 : $i]:
% 1.05/1.23         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.05/1.23      inference('cnf', [status(esa)], [d3_tarski])).
% 1.05/1.23  thf(t3_xboole_0, axiom,
% 1.05/1.23    (![A:$i,B:$i]:
% 1.05/1.23     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.05/1.23            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.05/1.23       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.05/1.23            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.05/1.23  thf('29', plain,
% 1.05/1.23      (![X6 : $i, X8 : $i, X9 : $i]:
% 1.05/1.23         (~ (r2_hidden @ X8 @ X6)
% 1.05/1.23          | ~ (r2_hidden @ X8 @ X9)
% 1.05/1.23          | ~ (r1_xboole_0 @ X6 @ X9))),
% 1.05/1.23      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.05/1.23  thf('30', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.23         ((r1_tarski @ X0 @ X1)
% 1.05/1.23          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.05/1.23          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 1.05/1.23      inference('sup-', [status(thm)], ['28', '29'])).
% 1.05/1.23  thf('31', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]:
% 1.05/1.23         ((r1_tarski @ X0 @ X1)
% 1.05/1.23          | ~ (r1_xboole_0 @ X0 @ X0)
% 1.05/1.23          | (r1_tarski @ X0 @ X1))),
% 1.05/1.23      inference('sup-', [status(thm)], ['27', '30'])).
% 1.05/1.23  thf('32', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (r1_tarski @ X0 @ X1))),
% 1.05/1.23      inference('simplify', [status(thm)], ['31'])).
% 1.05/1.23  thf('33', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.05/1.23      inference('sup-', [status(thm)], ['26', '32'])).
% 1.05/1.23  thf(t12_xboole_1, axiom,
% 1.05/1.23    (![A:$i,B:$i]:
% 1.05/1.23     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.05/1.23  thf('34', plain,
% 1.05/1.23      (![X10 : $i, X11 : $i]:
% 1.05/1.23         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 1.05/1.23      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.05/1.23  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.05/1.23      inference('sup-', [status(thm)], ['33', '34'])).
% 1.05/1.23  thf('36', plain,
% 1.05/1.23      (![X1 : $i, X3 : $i]:
% 1.05/1.23         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.05/1.23      inference('cnf', [status(esa)], [d3_tarski])).
% 1.05/1.23  thf(l27_zfmisc_1, axiom,
% 1.05/1.23    (![A:$i,B:$i]:
% 1.05/1.23     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.05/1.23  thf('37', plain,
% 1.05/1.23      (![X48 : $i, X49 : $i]:
% 1.05/1.23         ((r1_xboole_0 @ (k1_tarski @ X48) @ X49) | (r2_hidden @ X48 @ X49))),
% 1.05/1.23      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.05/1.23  thf('38', plain,
% 1.05/1.23      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.23      inference('sup-', [status(thm)], ['7', '12'])).
% 1.05/1.23  thf(t70_xboole_1, axiom,
% 1.05/1.23    (![A:$i,B:$i,C:$i]:
% 1.05/1.23     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.05/1.23            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.05/1.23       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.05/1.23            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.05/1.23  thf('39', plain,
% 1.05/1.23      (![X14 : $i, X15 : $i, X17 : $i]:
% 1.05/1.23         ((r1_xboole_0 @ X14 @ X17)
% 1.05/1.23          | ~ (r1_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X17)))),
% 1.05/1.23      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.05/1.23  thf('40', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         (~ (r1_xboole_0 @ X0 @ sk_B)
% 1.05/1.23          | ((sk_B) = (k1_xboole_0))
% 1.05/1.23          | (r1_xboole_0 @ X0 @ sk_C_2))),
% 1.05/1.23      inference('sup-', [status(thm)], ['38', '39'])).
% 1.05/1.23  thf('41', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         ((r2_hidden @ X0 @ sk_B)
% 1.05/1.23          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_C_2)
% 1.05/1.23          | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.23      inference('sup-', [status(thm)], ['37', '40'])).
% 1.05/1.23  thf(t69_enumset1, axiom,
% 1.05/1.23    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.05/1.23  thf('42', plain,
% 1.05/1.23      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 1.05/1.23      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.05/1.23  thf('43', plain,
% 1.05/1.23      (![X1 : $i, X3 : $i]:
% 1.05/1.23         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.05/1.23      inference('cnf', [status(esa)], [d3_tarski])).
% 1.05/1.23  thf('44', plain,
% 1.05/1.23      (![X1 : $i, X3 : $i]:
% 1.05/1.23         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.05/1.23      inference('cnf', [status(esa)], [d3_tarski])).
% 1.05/1.23  thf('45', plain,
% 1.05/1.23      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 1.05/1.23      inference('sup-', [status(thm)], ['43', '44'])).
% 1.05/1.23  thf('46', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.05/1.23      inference('simplify', [status(thm)], ['45'])).
% 1.05/1.23  thf(t38_zfmisc_1, axiom,
% 1.05/1.23    (![A:$i,B:$i,C:$i]:
% 1.05/1.23     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 1.05/1.23       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 1.05/1.23  thf('47', plain,
% 1.05/1.23      (![X55 : $i, X56 : $i, X57 : $i]:
% 1.05/1.23         ((r2_hidden @ X55 @ X56)
% 1.05/1.23          | ~ (r1_tarski @ (k2_tarski @ X55 @ X57) @ X56))),
% 1.05/1.23      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.05/1.23  thf('48', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 1.05/1.23      inference('sup-', [status(thm)], ['46', '47'])).
% 1.05/1.23  thf('49', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.05/1.23      inference('sup+', [status(thm)], ['42', '48'])).
% 1.05/1.23  thf('50', plain,
% 1.05/1.23      (![X6 : $i, X8 : $i, X9 : $i]:
% 1.05/1.23         (~ (r2_hidden @ X8 @ X6)
% 1.05/1.23          | ~ (r2_hidden @ X8 @ X9)
% 1.05/1.23          | ~ (r1_xboole_0 @ X6 @ X9))),
% 1.05/1.23      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.05/1.23  thf('51', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]:
% 1.05/1.23         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 1.05/1.23      inference('sup-', [status(thm)], ['49', '50'])).
% 1.05/1.23  thf('52', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         (((sk_B) = (k1_xboole_0))
% 1.05/1.23          | (r2_hidden @ X0 @ sk_B)
% 1.05/1.23          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 1.05/1.23      inference('sup-', [status(thm)], ['41', '51'])).
% 1.05/1.23  thf('53', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         ((r1_tarski @ sk_C_2 @ X0)
% 1.05/1.23          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_B)
% 1.05/1.23          | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.23      inference('sup-', [status(thm)], ['36', '52'])).
% 1.05/1.23  thf('54', plain,
% 1.05/1.23      (![X1 : $i, X3 : $i]:
% 1.05/1.23         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.05/1.23      inference('cnf', [status(esa)], [d3_tarski])).
% 1.05/1.23  thf('55', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0))
% 1.05/1.23        | (r1_tarski @ sk_C_2 @ sk_B)
% 1.05/1.23        | (r1_tarski @ sk_C_2 @ sk_B))),
% 1.05/1.23      inference('sup-', [status(thm)], ['53', '54'])).
% 1.05/1.23  thf('56', plain, (((r1_tarski @ sk_C_2 @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.23      inference('simplify', [status(thm)], ['55'])).
% 1.05/1.23  thf('57', plain,
% 1.05/1.23      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.23      inference('sup-', [status(thm)], ['7', '12'])).
% 1.05/1.23  thf('58', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 1.05/1.23          | ((X0) = (k1_xboole_0))
% 1.05/1.23          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 1.05/1.23      inference('demod', [status(thm)], ['10', '11'])).
% 1.05/1.23  thf('59', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         (~ (r1_tarski @ X0 @ sk_B)
% 1.05/1.23          | ((sk_B) = (k1_xboole_0))
% 1.05/1.23          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2))
% 1.05/1.23          | ((X0) = (k1_xboole_0)))),
% 1.05/1.23      inference('sup-', [status(thm)], ['57', '58'])).
% 1.05/1.23  thf('60', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0))
% 1.05/1.23        | ((sk_C_2) = (k1_xboole_0))
% 1.05/1.23        | ((sk_C_2) = (k2_xboole_0 @ sk_B @ sk_C_2))
% 1.05/1.23        | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.23      inference('sup-', [status(thm)], ['56', '59'])).
% 1.05/1.23  thf('61', plain,
% 1.05/1.23      ((((sk_C_2) = (k2_xboole_0 @ sk_B @ sk_C_2))
% 1.05/1.23        | ((sk_C_2) = (k1_xboole_0))
% 1.05/1.23        | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.23      inference('simplify', [status(thm)], ['60'])).
% 1.05/1.23  thf('62', plain,
% 1.05/1.23      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 1.05/1.23      inference('split', [status(esa)], ['15'])).
% 1.05/1.23  thf('63', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.05/1.23      inference('simplify', [status(thm)], ['18'])).
% 1.05/1.23  thf('64', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.05/1.23      inference('sup-', [status(thm)], ['33', '34'])).
% 1.05/1.23  thf('65', plain,
% 1.05/1.23      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 1.05/1.23         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.05/1.23      inference('sup+', [status(thm)], ['63', '64'])).
% 1.05/1.23  thf('66', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.05/1.23      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 1.05/1.23  thf('67', plain,
% 1.05/1.23      ((((sk_C_2) != (sk_C_2))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['65', '66'])).
% 1.05/1.23  thf('68', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 1.05/1.23      inference('simplify', [status(thm)], ['67'])).
% 1.05/1.23  thf('69', plain,
% 1.05/1.23      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 1.05/1.23      inference('split', [status(esa)], ['15'])).
% 1.05/1.23  thf('70', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 1.05/1.23      inference('sat_resolution*', [status(thm)], ['68', '69'])).
% 1.05/1.23  thf('71', plain, (((sk_C_2) != (k1_xboole_0))),
% 1.05/1.23      inference('simpl_trail', [status(thm)], ['62', '70'])).
% 1.05/1.23  thf('72', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.05/1.23      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 1.05/1.23  thf('73', plain, (((sk_B) = (k1_xboole_0))),
% 1.05/1.23      inference('simplify_reflect-', [status(thm)], ['61', '71', '72'])).
% 1.05/1.23  thf('74', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0))),
% 1.05/1.23      inference('demod', [status(thm)], ['35', '73'])).
% 1.05/1.23  thf('75', plain, (((sk_C_2) != (sk_C_2))),
% 1.05/1.23      inference('demod', [status(thm)], ['24', '74'])).
% 1.05/1.23  thf('76', plain, ($false), inference('simplify', [status(thm)], ['75'])).
% 1.05/1.23  
% 1.05/1.23  % SZS output end Refutation
% 1.05/1.23  
% 1.05/1.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.det0bnWa5K

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:31 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  160 (1970 expanded)
%              Number of leaves         :   23 ( 535 expanded)
%              Depth                    :   29
%              Number of atoms          : 1098 (20998 expanded)
%              Number of equality atoms :  163 (3616 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( X11 != X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( r2_hidden @ X53 @ X54 )
      | ~ ( r1_tarski @ ( k2_tarski @ X53 @ X55 ) @ X54 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('10',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('16',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('21',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( ( sk_C @ X0 @ sk_B_1 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['12','25'])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('35',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('38',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('39',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
    | ( ( k2_xboole_0 @ sk_B_1 @ sk_C_2 )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup+',[status(thm)],['1','39'])).

thf('41',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('44',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['44'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('46',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('48',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('50',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( sk_B @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('52',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('55',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('57',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('63',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['43','45','64'])).

thf('66',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['42','65'])).

thf('67',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['40','66'])).

thf('68',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','67'])).

thf('69',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','67'])).

thf('70',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('71',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('72',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','73'])).

thf('75',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('76',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('77',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k2_xboole_0 @ k1_xboole_0 @ sk_C_2 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('80',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['12','25'])).

thf('81',plain,
    ( ( ( r2_hidden @ sk_A @ k1_xboole_0 )
      | ( r1_tarski @ sk_B_1 @ sk_C_2 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('83',plain,
    ( ( ( r2_hidden @ sk_A @ k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ sk_C_2 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('85',plain,
    ( ( ( r1_tarski @ k1_xboole_0 @ sk_C_2 )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k2_xboole_0 @ k1_xboole_0 @ sk_C_2 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('87',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('88',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
      | ( ( k2_xboole_0 @ k1_xboole_0 @ sk_C_2 )
        = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k2_xboole_0 @ k1_xboole_0 @ sk_C_2 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('92',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['58'])).

thf('94',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('95',plain,
    ( ( k1_xboole_0
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['92','95'])).

thf('97',plain,
    ( ( r1_tarski @ k1_xboole_0 @ sk_C_2 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['85','96'])).

thf('98',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('99',plain,
    ( ( ( k2_xboole_0 @ k1_xboole_0 @ sk_C_2 )
      = sk_C_2 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['78','99'])).

thf('101',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['42','65'])).

thf('102',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['58'])).

thf('104',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['102','103'])).

thf('105',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['75','104'])).

thf('106',plain,(
    r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['74','105'])).

thf('107',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['40','66'])).

thf('108',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['40','66'])).

thf('109',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('110',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('113',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['111','114'])).

thf('116',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['108','115'])).

thf('117',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['107','116'])).

thf('118',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0
        = ( k3_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( sk_B @ sk_C_2 )
    = ( k3_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['106','119'])).

thf('121',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) @ sk_C_2 )
      = sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['120','125'])).

thf('127',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['107','116'])).

thf('128',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_C_2 )
      = sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['75','104'])).

thf('130',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_2 )
    = sk_C_2 ),
    inference('simplify_reflect-',[status(thm)],['128','129'])).

thf('131',plain,(
    sk_B_1 = sk_C_2 ),
    inference('sup+',[status(thm)],['68','130'])).

thf('132',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['42','65'])).

thf('133',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['40','66'])).

thf('134',plain,(
    sk_C_2 != sk_B_1 ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['131','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.det0bnWa5K
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:38:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 404 iterations in 0.190s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.65  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.65  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(t43_zfmisc_1, conjecture,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.46/0.65          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.46/0.65          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.46/0.65          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.65        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.46/0.65             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.46/0.65             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.46/0.65             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.46/0.65  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t69_enumset1, axiom,
% 0.46/0.65    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.65  thf('2', plain, (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.46/0.65      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.65  thf(d10_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (![X11 : $i, X12 : $i]: ((r1_tarski @ X11 @ X12) | ((X11) != (X12)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.65  thf('4', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 0.46/0.65      inference('simplify', [status(thm)], ['3'])).
% 0.46/0.65  thf(t38_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.46/0.65       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.46/0.65         ((r2_hidden @ X53 @ X54)
% 0.46/0.65          | ~ (r1_tarski @ (k2_tarski @ X53 @ X55) @ X54))),
% 0.46/0.65      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.65  thf('7', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['2', '6'])).
% 0.46/0.65  thf('8', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(d3_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.46/0.65       ( ![D:$i]:
% 0.46/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.65           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X8 @ X6)
% 0.46/0.65          | (r2_hidden @ X8 @ X7)
% 0.46/0.65          | (r2_hidden @ X8 @ X5)
% 0.46/0.65          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.46/0.65         ((r2_hidden @ X8 @ X5)
% 0.46/0.65          | (r2_hidden @ X8 @ X7)
% 0.46/0.65          | ~ (r2_hidden @ X8 @ (k2_xboole_0 @ X7 @ X5)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['9'])).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.46/0.65          | (r2_hidden @ X0 @ sk_B_1)
% 0.46/0.65          | (r2_hidden @ X0 @ sk_C_2))),
% 0.46/0.65      inference('sup-', [status(thm)], ['8', '10'])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (((r2_hidden @ sk_A @ sk_C_2) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['7', '11'])).
% 0.46/0.65  thf(d3_tarski, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.65  thf('13', plain,
% 0.46/0.65      (![X1 : $i, X3 : $i]:
% 0.46/0.65         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.65  thf('14', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t7_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.46/0.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.65  thf('16', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['14', '15'])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.65          | (r2_hidden @ X0 @ X2)
% 0.46/0.65          | ~ (r1_tarski @ X1 @ X2))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r1_tarski @ sk_B_1 @ X0)
% 0.46/0.65          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['13', '18'])).
% 0.46/0.65  thf(d1_tarski, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.46/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X21 @ X20)
% 0.46/0.65          | ((X21) = (X18))
% 0.46/0.65          | ((X20) != (k1_tarski @ X18)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_tarski])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      (![X18 : $i, X21 : $i]:
% 0.46/0.65         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['20'])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r1_tarski @ sk_B_1 @ X0) | ((sk_C @ X0 @ sk_B_1) = (sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['19', '21'])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      (![X1 : $i, X3 : $i]:
% 0.46/0.65         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r2_hidden @ sk_A @ X0)
% 0.46/0.65          | (r1_tarski @ sk_B_1 @ X0)
% 0.46/0.65          | (r1_tarski @ sk_B_1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['24'])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      (((r2_hidden @ sk_A @ sk_B_1) | (r1_tarski @ sk_B_1 @ sk_C_2))),
% 0.46/0.65      inference('sup-', [status(thm)], ['12', '25'])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (![X1 : $i, X3 : $i]:
% 0.46/0.65         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (![X18 : $i, X21 : $i]:
% 0.46/0.65         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['20'])).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.46/0.65          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      (![X1 : $i, X3 : $i]:
% 0.46/0.65         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.65          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.46/0.65          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.46/0.65      inference('simplify', [status(thm)], ['31'])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (((r1_tarski @ sk_B_1 @ sk_C_2)
% 0.46/0.65        | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['26', '32'])).
% 0.46/0.65  thf('34', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['14', '15'])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      (![X11 : $i, X13 : $i]:
% 0.46/0.65         (((X11) = (X13))
% 0.46/0.65          | ~ (r1_tarski @ X13 @ X11)
% 0.46/0.65          | ~ (r1_tarski @ X11 @ X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.46/0.65        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      (((r1_tarski @ sk_B_1 @ sk_C_2) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['33', '36'])).
% 0.46/0.65  thf(t12_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.46/0.65      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      ((((k1_tarski @ sk_A) = (sk_B_1))
% 0.46/0.65        | ((k2_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      ((((k1_tarski @ sk_A) = (sk_C_2)) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['1', '39'])).
% 0.46/0.65  thf('41', plain,
% 0.46/0.65      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.46/0.65         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.46/0.65      inference('split', [status(esa)], ['41'])).
% 0.46/0.65  thf('43', plain,
% 0.46/0.65      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.46/0.65      inference('split', [status(esa)], ['41'])).
% 0.46/0.65  thf('44', plain,
% 0.46/0.65      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('45', plain,
% 0.46/0.65      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | 
% 0.46/0.65       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.46/0.65      inference('split', [status(esa)], ['44'])).
% 0.46/0.65  thf(t7_xboole_0, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.65          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.65  thf('46', plain,
% 0.46/0.65      (![X10 : $i]:
% 0.46/0.65         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.46/0.65      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.65  thf('48', plain,
% 0.46/0.65      ((((sk_B_1) = (k1_xboole_0))
% 0.46/0.65        | (r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['46', '47'])).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      (![X18 : $i, X21 : $i]:
% 0.46/0.65         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['20'])).
% 0.46/0.65  thf('50', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_B @ sk_B_1) = (sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.65  thf('51', plain,
% 0.46/0.65      (![X10 : $i]:
% 0.46/0.65         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.46/0.65      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      (((r2_hidden @ sk_A @ sk_B_1)
% 0.46/0.65        | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.65        | ((sk_B_1) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['50', '51'])).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      ((((sk_B_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.46/0.65      inference('simplify', [status(thm)], ['52'])).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.46/0.65      inference('simplify', [status(thm)], ['31'])).
% 0.46/0.65  thf('55', plain,
% 0.46/0.65      ((((sk_B_1) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.46/0.65        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      ((((sk_B_1) = (k1_xboole_0)) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('59', plain,
% 0.46/0.65      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.46/0.65         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.65      inference('split', [status(esa)], ['58'])).
% 0.46/0.65  thf('60', plain,
% 0.46/0.65      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 0.46/0.65         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['57', '59'])).
% 0.46/0.65  thf('61', plain,
% 0.46/0.65      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.65      inference('simplify', [status(thm)], ['60'])).
% 0.46/0.65  thf('62', plain,
% 0.46/0.65      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['41'])).
% 0.46/0.65  thf('63', plain,
% 0.46/0.65      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.46/0.65         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.46/0.65             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['61', '62'])).
% 0.46/0.65  thf('64', plain,
% 0.46/0.65      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['63'])).
% 0.46/0.65  thf('65', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.46/0.65      inference('sat_resolution*', [status(thm)], ['43', '45', '64'])).
% 0.46/0.65  thf('66', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['42', '65'])).
% 0.46/0.65  thf('67', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['40', '66'])).
% 0.46/0.65  thf('68', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.46/0.65      inference('demod', [status(thm)], ['0', '67'])).
% 0.46/0.65  thf('69', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.46/0.65      inference('demod', [status(thm)], ['0', '67'])).
% 0.46/0.65  thf('70', plain,
% 0.46/0.65      (![X10 : $i]:
% 0.46/0.65         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.46/0.65      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.65  thf('71', plain,
% 0.46/0.65      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X4 @ X5)
% 0.46/0.65          | (r2_hidden @ X4 @ X6)
% 0.46/0.65          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.46/0.65  thf('72', plain,
% 0.46/0.65      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.46/0.65         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.46/0.65      inference('simplify', [status(thm)], ['71'])).
% 0.46/0.65  thf('73', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (((X0) = (k1_xboole_0))
% 0.46/0.65          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['70', '72'])).
% 0.46/0.65  thf('74', plain,
% 0.46/0.65      (((r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1) | ((sk_C_2) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['69', '73'])).
% 0.46/0.65  thf('75', plain,
% 0.46/0.65      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['58'])).
% 0.46/0.65  thf('76', plain,
% 0.46/0.65      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.65      inference('simplify', [status(thm)], ['60'])).
% 0.46/0.65  thf('77', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('78', plain,
% 0.46/0.65      ((((k1_tarski @ sk_A) = (k2_xboole_0 @ k1_xboole_0 @ sk_C_2)))
% 0.46/0.65         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.65      inference('sup+', [status(thm)], ['76', '77'])).
% 0.46/0.65  thf('79', plain,
% 0.46/0.65      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.65      inference('simplify', [status(thm)], ['60'])).
% 0.46/0.65  thf('80', plain,
% 0.46/0.65      (((r2_hidden @ sk_A @ sk_B_1) | (r1_tarski @ sk_B_1 @ sk_C_2))),
% 0.46/0.65      inference('sup-', [status(thm)], ['12', '25'])).
% 0.46/0.65  thf('81', plain,
% 0.46/0.65      ((((r2_hidden @ sk_A @ k1_xboole_0) | (r1_tarski @ sk_B_1 @ sk_C_2)))
% 0.46/0.65         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.65      inference('sup+', [status(thm)], ['79', '80'])).
% 0.46/0.65  thf('82', plain,
% 0.46/0.65      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.65      inference('simplify', [status(thm)], ['60'])).
% 0.46/0.65  thf('83', plain,
% 0.46/0.65      ((((r2_hidden @ sk_A @ k1_xboole_0) | (r1_tarski @ k1_xboole_0 @ sk_C_2)))
% 0.46/0.65         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.65      inference('demod', [status(thm)], ['81', '82'])).
% 0.46/0.65  thf('84', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.46/0.65      inference('simplify', [status(thm)], ['31'])).
% 0.46/0.65  thf('85', plain,
% 0.46/0.65      ((((r1_tarski @ k1_xboole_0 @ sk_C_2)
% 0.46/0.65         | (r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0)))
% 0.46/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['83', '84'])).
% 0.46/0.66  thf('86', plain,
% 0.46/0.66      ((((k1_tarski @ sk_A) = (k2_xboole_0 @ k1_xboole_0 @ sk_C_2)))
% 0.46/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['76', '77'])).
% 0.46/0.66  thf('87', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.66  thf('88', plain,
% 0.46/0.66      (![X11 : $i, X13 : $i]:
% 0.46/0.66         (((X11) = (X13))
% 0.46/0.66          | ~ (r1_tarski @ X13 @ X11)
% 0.46/0.66          | ~ (r1_tarski @ X11 @ X13))),
% 0.46/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.66  thf('89', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.46/0.66          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['87', '88'])).
% 0.46/0.66  thf('90', plain,
% 0.46/0.66      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 0.46/0.66         | ((k2_xboole_0 @ k1_xboole_0 @ sk_C_2) = (k1_xboole_0))))
% 0.46/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['86', '89'])).
% 0.46/0.66  thf('91', plain,
% 0.46/0.66      ((((k1_tarski @ sk_A) = (k2_xboole_0 @ k1_xboole_0 @ sk_C_2)))
% 0.46/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['76', '77'])).
% 0.46/0.66  thf('92', plain,
% 0.46/0.66      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 0.46/0.66         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.46/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('demod', [status(thm)], ['90', '91'])).
% 0.46/0.66  thf('93', plain,
% 0.46/0.66      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.46/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('split', [status(esa)], ['58'])).
% 0.46/0.66  thf('94', plain,
% 0.46/0.66      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['60'])).
% 0.46/0.66  thf('95', plain,
% 0.46/0.66      ((((k1_xboole_0) != (k1_tarski @ sk_A)))
% 0.46/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('demod', [status(thm)], ['93', '94'])).
% 0.46/0.66  thf('96', plain,
% 0.46/0.66      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0))
% 0.46/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['92', '95'])).
% 0.46/0.66  thf('97', plain,
% 0.46/0.66      (((r1_tarski @ k1_xboole_0 @ sk_C_2))
% 0.46/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('clc', [status(thm)], ['85', '96'])).
% 0.46/0.66  thf('98', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i]:
% 0.46/0.66         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.46/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.66  thf('99', plain,
% 0.46/0.66      ((((k2_xboole_0 @ k1_xboole_0 @ sk_C_2) = (sk_C_2)))
% 0.46/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['97', '98'])).
% 0.46/0.66  thf('100', plain,
% 0.46/0.66      ((((k1_tarski @ sk_A) = (sk_C_2)))
% 0.46/0.66         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['78', '99'])).
% 0.46/0.66  thf('101', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['42', '65'])).
% 0.46/0.66  thf('102', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['100', '101'])).
% 0.46/0.66  thf('103', plain,
% 0.46/0.66      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['58'])).
% 0.46/0.66  thf('104', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.46/0.66      inference('sat_resolution*', [status(thm)], ['102', '103'])).
% 0.46/0.66  thf('105', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['75', '104'])).
% 0.46/0.66  thf('106', plain, ((r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1)),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['74', '105'])).
% 0.46/0.66  thf('107', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['40', '66'])).
% 0.46/0.66  thf('108', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['40', '66'])).
% 0.46/0.66  thf('109', plain,
% 0.46/0.66      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.46/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.66  thf(l51_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.66  thf('110', plain,
% 0.46/0.66      (![X51 : $i, X52 : $i]:
% 0.46/0.66         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 0.46/0.66      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.66  thf('111', plain,
% 0.46/0.66      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['109', '110'])).
% 0.46/0.66  thf('112', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 0.46/0.66      inference('simplify', [status(thm)], ['3'])).
% 0.46/0.66  thf('113', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i]:
% 0.46/0.66         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.46/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.66  thf('114', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['112', '113'])).
% 0.46/0.66  thf('115', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['111', '114'])).
% 0.46/0.66  thf('116', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 0.46/0.66      inference('sup+', [status(thm)], ['108', '115'])).
% 0.46/0.66  thf('117', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 0.46/0.66      inference('demod', [status(thm)], ['107', '116'])).
% 0.46/0.66  thf('118', plain,
% 0.46/0.66      (![X18 : $i, X21 : $i]:
% 0.46/0.66         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['20'])).
% 0.46/0.66  thf('119', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (k3_tarski @ sk_B_1)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['117', '118'])).
% 0.46/0.66  thf('120', plain, (((sk_B @ sk_C_2) = (k3_tarski @ sk_B_1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['106', '119'])).
% 0.46/0.66  thf('121', plain,
% 0.46/0.66      (![X10 : $i]:
% 0.46/0.66         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.66  thf('122', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.46/0.66      inference('simplify', [status(thm)], ['31'])).
% 0.46/0.66  thf('123', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['121', '122'])).
% 0.46/0.66  thf('124', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i]:
% 0.46/0.66         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.46/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.66  thf('125', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((X0) = (k1_xboole_0))
% 0.46/0.66          | ((k2_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ X0) = (X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['123', '124'])).
% 0.46/0.66  thf('126', plain,
% 0.46/0.66      ((((k2_xboole_0 @ (k1_tarski @ (k3_tarski @ sk_B_1)) @ sk_C_2) = (sk_C_2))
% 0.46/0.66        | ((sk_C_2) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['120', '125'])).
% 0.46/0.66  thf('127', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 0.46/0.66      inference('demod', [status(thm)], ['107', '116'])).
% 0.46/0.66  thf('128', plain,
% 0.46/0.66      ((((k2_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))
% 0.46/0.66        | ((sk_C_2) = (k1_xboole_0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['126', '127'])).
% 0.46/0.66  thf('129', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['75', '104'])).
% 0.46/0.66  thf('130', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['128', '129'])).
% 0.46/0.66  thf('131', plain, (((sk_B_1) = (sk_C_2))),
% 0.46/0.66      inference('sup+', [status(thm)], ['68', '130'])).
% 0.46/0.66  thf('132', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['42', '65'])).
% 0.46/0.66  thf('133', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['40', '66'])).
% 0.46/0.66  thf('134', plain, (((sk_C_2) != (sk_B_1))),
% 0.46/0.66      inference('demod', [status(thm)], ['132', '133'])).
% 0.46/0.66  thf('135', plain, ($false),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['131', '134'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

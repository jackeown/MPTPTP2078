%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jkEfPrerI5

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 330 expanded)
%              Number of leaves         :   27 ( 110 expanded)
%              Depth                    :   16
%              Number of atoms          :  663 (2716 expanded)
%              Number of equality atoms :   54 ( 153 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t27_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( ( k2_tarski @ A @ B )
        = ( k1_tarski @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( ( k2_tarski @ A @ B )
          = ( k1_tarski @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X32
        = ( k2_xboole_0 @ X31 @ ( k4_xboole_0 @ X32 @ X31 ) ) )
      | ~ ( r1_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('2',plain,
    ( ( k1_tarski @ sk_C_2 )
    = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_C_2 ) @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X44: $i,X45: $i] :
      ( r1_tarski @ ( k1_tarski @ X44 ) @ ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('4',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X47 ) @ ( k1_tarski @ X48 ) )
        = ( k1_tarski @ X47 ) )
      | ( X47 = X48 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X35: $i,X37: $i] :
      ( ( r1_xboole_0 @ X35 @ X37 )
      | ( ( k4_xboole_0 @ X35 @ X37 )
       != X35 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

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

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_C_2 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_C_2 ) @ X0 )
      | ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_C_2 ) @ X0 )
      | ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 = X0 )
      | ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('19',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k4_xboole_0 @ X35 @ X36 )
        = X35 )
      | ~ ( r1_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 = X0 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( r1_tarski @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( sk_C_2 = X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X46: $i,X47: $i] :
      ( ( X47 != X46 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X47 ) @ ( k1_tarski @ X46 ) )
       != ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('24',plain,(
    ! [X46: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X46 ) @ ( k1_tarski @ X46 ) )
     != ( k1_tarski @ X46 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X32
        = ( k2_xboole_0 @ X31 @ ( k4_xboole_0 @ X32 @ X31 ) ) )
      | ~ ( r1_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ( r1_tarski @ X17 @ ( k2_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('39',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['25','40'])).

thf('42',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( r1_tarski @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X46: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X46 ) ) ),
    inference(demod,[status(thm)],['24','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['22','44'])).

thf('46',plain,(
    sk_C_2 = sk_A ),
    inference('sup-',[status(thm)],['3','45'])).

thf('47',plain,(
    sk_C_2 = sk_A ),
    inference('sup-',[status(thm)],['3','45'])).

thf('48',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('51',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t24_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ) )).

thf('52',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k3_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ ( k2_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('54',plain,(
    ! [X28: $i] :
      ( ( k3_xboole_0 @ X28 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('55',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['48','56'])).

thf('58',plain,(
    ! [X44: $i,X45: $i] :
      ( r1_tarski @ ( k1_tarski @ X44 ) @ ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('59',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    sk_C_2 = sk_A ),
    inference('sup-',[status(thm)],['3','45'])).

thf('64',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jkEfPrerI5
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 197 iterations in 0.078s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.52  thf(t27_zfmisc_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.20/0.52       ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.52        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.20/0.52          ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t27_zfmisc_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C_2))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t45_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.52       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X31 : $i, X32 : $i]:
% 0.20/0.52         (((X32) = (k2_xboole_0 @ X31 @ (k4_xboole_0 @ X32 @ X31)))
% 0.20/0.52          | ~ (r1_tarski @ X31 @ X32))),
% 0.20/0.52      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (((k1_tarski @ sk_C_2)
% 0.20/0.52         = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52            (k4_xboole_0 @ (k1_tarski @ sk_C_2) @ (k2_tarski @ sk_A @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf(t12_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X44 : $i, X45 : $i]:
% 0.20/0.52         (r1_tarski @ (k1_tarski @ X44) @ (k2_tarski @ X44 @ X45))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.20/0.52  thf(t20_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.52         ( k1_tarski @ A ) ) <=>
% 0.20/0.52       ( ( A ) != ( B ) ) ))).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X47 : $i, X48 : $i]:
% 0.20/0.52         (((k4_xboole_0 @ (k1_tarski @ X47) @ (k1_tarski @ X48))
% 0.20/0.52            = (k1_tarski @ X47))
% 0.20/0.52          | ((X47) = (X48)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.52  thf(t83_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X35 : $i, X37 : $i]:
% 0.20/0.52         ((r1_xboole_0 @ X35 @ X37) | ((k4_xboole_0 @ X35 @ X37) != (X35)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.20/0.52          | ((X0) = (X1))
% 0.20/0.52          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.52  thf(t3_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C_2))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d3_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.52          | (r2_hidden @ X0 @ X2)
% 0.20/0.52          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ X0 @ (k1_tarski @ sk_C_2))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 0.20/0.52          | (r2_hidden @ (sk_C_1 @ X0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.20/0.52             (k1_tarski @ sk_C_2)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X12 @ X10)
% 0.20/0.52          | ~ (r2_hidden @ X12 @ X13)
% 0.20/0.52          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 0.20/0.52          | ~ (r1_xboole_0 @ (k1_tarski @ sk_C_2) @ X1)
% 0.20/0.52          | ~ (r2_hidden @ (sk_C_1 @ X0 @ (k2_tarski @ sk_A @ sk_B)) @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 0.20/0.52          | ~ (r1_xboole_0 @ (k1_tarski @ sk_C_2) @ X0)
% 0.20/0.52          | (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['8', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r1_xboole_0 @ (k1_tarski @ sk_C_2) @ X0)
% 0.20/0.52          | (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((sk_C_2) = (X0))
% 0.20/0.52          | (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X35 : $i, X36 : $i]:
% 0.20/0.52         (((k4_xboole_0 @ X35 @ X36) = (X35)) | ~ (r1_xboole_0 @ X35 @ X36))),
% 0.20/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((sk_C_2) = (X0))
% 0.20/0.52          | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ X0))
% 0.20/0.52              = (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf(t38_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.20/0.52       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X29 : $i, X30 : $i]:
% 0.20/0.52         (((X29) = (k1_xboole_0))
% 0.20/0.52          | ~ (r1_tarski @ X29 @ (k4_xboole_0 @ X30 @ X29)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ sk_A @ sk_B))
% 0.20/0.52          | ((sk_C_2) = (X0))
% 0.20/0.52          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X46 : $i, X47 : $i]:
% 0.20/0.52         (((X47) != (X46))
% 0.20/0.52          | ((k4_xboole_0 @ (k1_tarski @ X47) @ (k1_tarski @ X46))
% 0.20/0.52              != (k1_tarski @ X47)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X46 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ (k1_tarski @ X46) @ (k1_tarski @ X46))
% 0.20/0.52           != (k1_tarski @ X46))),
% 0.20/0.52      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.52      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (![X31 : $i, X32 : $i]:
% 0.20/0.52         (((X32) = (k2_xboole_0 @ X31 @ (k4_xboole_0 @ X32 @ X31)))
% 0.20/0.52          | ~ (r1_tarski @ X31 @ X32))),
% 0.20/0.52      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('32', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.52      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.52  thf(t10_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.52         (~ (r1_tarski @ X17 @ X18)
% 0.20/0.52          | (r1_tarski @ X17 @ (k2_xboole_0 @ X19 @ X18)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('35', plain, (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X0)),
% 0.20/0.52      inference('sup+', [status(thm)], ['31', '34'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.52          | (r2_hidden @ X0 @ X2)
% 0.20/0.52          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf(d5_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.52       ( ![D:$i]:
% 0.20/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.52           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X8 @ X7)
% 0.20/0.52          | ~ (r2_hidden @ X8 @ X6)
% 0.20/0.52          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X8 @ X6)
% 0.20/0.52          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.20/0.52      inference('clc', [status(thm)], ['37', '39'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.20/0.52      inference('sup-', [status(thm)], ['25', '40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X29 : $i, X30 : $i]:
% 0.20/0.52         (((X29) = (k1_xboole_0))
% 0.20/0.52          | ~ (r1_tarski @ X29 @ (k4_xboole_0 @ X30 @ X29)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.20/0.52  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf('44', plain, (![X46 : $i]: ((k1_xboole_0) != (k1_tarski @ X46))),
% 0.20/0.52      inference('demod', [status(thm)], ['24', '43'])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((sk_C_2) = (X0))
% 0.20/0.52          | ~ (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.52      inference('clc', [status(thm)], ['22', '44'])).
% 0.20/0.52  thf('46', plain, (((sk_C_2) = (sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '45'])).
% 0.20/0.52  thf('47', plain, (((sk_C_2) = (sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '45'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (((k1_tarski @ sk_A)
% 0.20/0.52         = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52            (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['2', '46', '47'])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf('51', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.52  thf(t24_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.20/0.52       ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ))).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ X23 @ (k3_xboole_0 @ X24 @ X25))
% 0.20/0.52           = (k3_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ 
% 0.20/0.52              (k2_xboole_0 @ X23 @ X25)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t24_xboole_1])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ k1_xboole_0))
% 0.20/0.52           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['51', '52'])).
% 0.20/0.52  thf(t2_boole, axiom,
% 0.20/0.52    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (![X28 : $i]: ((k3_xboole_0 @ X28 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.52  thf('55', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((X0) = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      (((k2_tarski @ sk_A @ sk_B)
% 0.20/0.52         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['48', '56'])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      (![X44 : $i, X45 : $i]:
% 0.20/0.52         (r1_tarski @ (k1_tarski @ X44) @ (k2_tarski @ X44 @ X45))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.20/0.52  thf(t28_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      (![X26 : $i, X27 : $i]:
% 0.20/0.52         (((k3_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_tarski @ X26 @ X27))),
% 0.20/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.52  thf('60', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.20/0.52           = (k1_tarski @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.52  thf('61', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['57', '60'])).
% 0.20/0.52  thf('62', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_C_2))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('63', plain, (((sk_C_2) = (sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '45'])).
% 0.20/0.52  thf('64', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.52  thf('65', plain, ($false),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['61', '64'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

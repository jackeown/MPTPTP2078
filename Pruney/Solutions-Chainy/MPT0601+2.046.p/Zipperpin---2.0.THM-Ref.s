%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CTXRhtJLXj

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:47 EST 2020

% Result     : Theorem 3.02s
% Output     : Refutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 181 expanded)
%              Number of leaves         :   19 (  60 expanded)
%              Depth                    :   21
%              Number of atoms          :  730 (1501 expanded)
%              Number of equality atoms :   50 ( 103 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9
        = ( k1_relat_1 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X9 @ X6 ) @ ( sk_D @ X9 @ X6 ) ) @ X6 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X6 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('7',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('10',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D_1 @ X8 @ X6 ) ) @ X6 )
      | ( X7
       != ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('14',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D_1 @ X8 @ X6 ) ) @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B ) ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X11 ) @ X12 )
      | ( r2_hidden @ X11 @ ( k11_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('17',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k11_relat_1 @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('21',plain,
    ( ~ ( v1_xboole_0 @ ( k11_relat_1 @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','21'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('24',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['9','24'])).

thf('26',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['8','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('29',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k11_relat_1 @ X12 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 ) @ X2 )
      | ( X2
        = ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X1
        = ( k11_relat_1 @ X0 @ X2 ) )
      | ( r2_hidden @ ( sk_C @ ( k11_relat_1 @ X0 @ X2 ) @ X1 ) @ X1 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9
        = ( k1_relat_1 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X9 @ X6 ) @ ( sk_D @ X9 @ X6 ) ) @ X6 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X6 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('36',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D_1 @ X8 @ X6 ) ) @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_D_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(condensation,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('45',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D_1 @ X8 @ X6 ) ) @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
      | ( ( k1_relat_1 @ X0 )
        = X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k1_relat_1 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k1_relat_1 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = X1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['33','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k11_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k11_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','56'])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k11_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('62',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('63',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['9','24','62'])).

thf('64',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['61','63'])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k11_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = ( k11_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ( k1_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['26','67'])).

thf('69',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','68'])).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('71',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference(simplify,[status(thm)],['71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CTXRhtJLXj
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:23:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 3.02/3.24  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.02/3.24  % Solved by: fo/fo7.sh
% 3.02/3.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.02/3.24  % done 1389 iterations in 2.793s
% 3.02/3.24  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.02/3.24  % SZS output start Refutation
% 3.02/3.24  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.02/3.24  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 3.02/3.24  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.02/3.24  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.02/3.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.02/3.24  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.02/3.24  thf(sk_B_type, type, sk_B: $i).
% 3.02/3.24  thf(sk_A_type, type, sk_A: $i).
% 3.02/3.24  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.02/3.24  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 3.02/3.24  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 3.02/3.24  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.02/3.24  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.02/3.24  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.02/3.24  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.02/3.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.02/3.24  thf(d4_relat_1, axiom,
% 3.02/3.24    (![A:$i,B:$i]:
% 3.02/3.24     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 3.02/3.24       ( ![C:$i]:
% 3.02/3.24         ( ( r2_hidden @ C @ B ) <=>
% 3.02/3.24           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 3.02/3.24  thf('1', plain,
% 3.02/3.24      (![X6 : $i, X9 : $i]:
% 3.02/3.24         (((X9) = (k1_relat_1 @ X6))
% 3.02/3.24          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X9 @ X6) @ (sk_D @ X9 @ X6)) @ 
% 3.02/3.24             X6)
% 3.02/3.24          | (r2_hidden @ (sk_C_1 @ X9 @ X6) @ X9))),
% 3.02/3.24      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.02/3.24  thf(t7_boole, axiom,
% 3.02/3.24    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 3.02/3.24  thf('2', plain,
% 3.02/3.24      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 3.02/3.24      inference('cnf', [status(esa)], [t7_boole])).
% 3.02/3.24  thf('3', plain,
% 3.02/3.24      (![X0 : $i, X1 : $i]:
% 3.02/3.24         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 3.02/3.24          | ((X1) = (k1_relat_1 @ X0))
% 3.02/3.24          | ~ (v1_xboole_0 @ X0))),
% 3.02/3.24      inference('sup-', [status(thm)], ['1', '2'])).
% 3.02/3.24  thf('4', plain,
% 3.02/3.24      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 3.02/3.24      inference('cnf', [status(esa)], [t7_boole])).
% 3.02/3.24  thf('5', plain,
% 3.02/3.24      (![X0 : $i, X1 : $i]:
% 3.02/3.24         (~ (v1_xboole_0 @ X1)
% 3.02/3.24          | ((X0) = (k1_relat_1 @ X1))
% 3.02/3.24          | ~ (v1_xboole_0 @ X0))),
% 3.02/3.24      inference('sup-', [status(thm)], ['3', '4'])).
% 3.02/3.24  thf('6', plain,
% 3.02/3.24      (![X0 : $i]: (((k1_xboole_0) = (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 3.02/3.24      inference('sup-', [status(thm)], ['0', '5'])).
% 3.02/3.24  thf(t205_relat_1, conjecture,
% 3.02/3.24    (![A:$i,B:$i]:
% 3.02/3.24     ( ( v1_relat_1 @ B ) =>
% 3.02/3.24       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 3.02/3.24         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 3.02/3.24  thf(zf_stmt_0, negated_conjecture,
% 3.02/3.24    (~( ![A:$i,B:$i]:
% 3.02/3.24        ( ( v1_relat_1 @ B ) =>
% 3.02/3.24          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 3.02/3.24            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 3.02/3.24    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 3.02/3.24  thf('7', plain,
% 3.02/3.24      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))
% 3.02/3.24        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 3.02/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.24  thf('8', plain,
% 3.02/3.24      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 3.02/3.24         <= (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 3.02/3.24      inference('split', [status(esa)], ['7'])).
% 3.02/3.24  thf('9', plain,
% 3.02/3.24      (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 3.02/3.24       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 3.02/3.24      inference('split', [status(esa)], ['7'])).
% 3.02/3.24  thf('10', plain,
% 3.02/3.24      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 3.02/3.24        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 3.02/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.24  thf('11', plain,
% 3.02/3.24      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 3.02/3.24         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 3.02/3.24      inference('split', [status(esa)], ['10'])).
% 3.02/3.24  thf('12', plain,
% 3.02/3.24      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 3.02/3.24         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 3.02/3.24      inference('split', [status(esa)], ['7'])).
% 3.02/3.24  thf('13', plain,
% 3.02/3.24      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.02/3.24         (~ (r2_hidden @ X8 @ X7)
% 3.02/3.24          | (r2_hidden @ (k4_tarski @ X8 @ (sk_D_1 @ X8 @ X6)) @ X6)
% 3.02/3.24          | ((X7) != (k1_relat_1 @ X6)))),
% 3.02/3.24      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.02/3.24  thf('14', plain,
% 3.02/3.24      (![X6 : $i, X8 : $i]:
% 3.02/3.24         ((r2_hidden @ (k4_tarski @ X8 @ (sk_D_1 @ X8 @ X6)) @ X6)
% 3.02/3.24          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X6)))),
% 3.02/3.24      inference('simplify', [status(thm)], ['13'])).
% 3.02/3.24  thf('15', plain,
% 3.02/3.24      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B)) @ sk_B))
% 3.02/3.24         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 3.02/3.24      inference('sup-', [status(thm)], ['12', '14'])).
% 3.02/3.24  thf(t204_relat_1, axiom,
% 3.02/3.24    (![A:$i,B:$i,C:$i]:
% 3.02/3.24     ( ( v1_relat_1 @ C ) =>
% 3.02/3.24       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 3.02/3.24         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 3.02/3.24  thf('16', plain,
% 3.02/3.24      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.02/3.24         (~ (r2_hidden @ (k4_tarski @ X13 @ X11) @ X12)
% 3.02/3.24          | (r2_hidden @ X11 @ (k11_relat_1 @ X12 @ X13))
% 3.02/3.24          | ~ (v1_relat_1 @ X12))),
% 3.02/3.24      inference('cnf', [status(esa)], [t204_relat_1])).
% 3.02/3.24  thf('17', plain,
% 3.02/3.24      (((~ (v1_relat_1 @ sk_B)
% 3.02/3.24         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A))))
% 3.02/3.24         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 3.02/3.24      inference('sup-', [status(thm)], ['15', '16'])).
% 3.02/3.24  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 3.02/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.24  thf('19', plain,
% 3.02/3.24      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k11_relat_1 @ sk_B @ sk_A)))
% 3.02/3.24         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 3.02/3.24      inference('demod', [status(thm)], ['17', '18'])).
% 3.02/3.24  thf('20', plain,
% 3.02/3.24      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 3.02/3.24      inference('cnf', [status(esa)], [t7_boole])).
% 3.02/3.24  thf('21', plain,
% 3.02/3.24      ((~ (v1_xboole_0 @ (k11_relat_1 @ sk_B @ sk_A)))
% 3.02/3.24         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 3.02/3.24      inference('sup-', [status(thm)], ['19', '20'])).
% 3.02/3.24  thf('22', plain,
% 3.02/3.24      ((~ (v1_xboole_0 @ k1_xboole_0))
% 3.02/3.24         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 3.02/3.24             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 3.02/3.24      inference('sup-', [status(thm)], ['11', '21'])).
% 3.02/3.24  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.02/3.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.02/3.24  thf('24', plain,
% 3.02/3.24      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 3.02/3.24       ~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 3.02/3.24      inference('demod', [status(thm)], ['22', '23'])).
% 3.02/3.24  thf('25', plain, (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 3.02/3.24      inference('sat_resolution*', [status(thm)], ['9', '24'])).
% 3.02/3.24  thf('26', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 3.02/3.24      inference('simpl_trail', [status(thm)], ['8', '25'])).
% 3.02/3.24  thf('27', plain,
% 3.02/3.24      (![X0 : $i]: (((k1_xboole_0) = (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 3.02/3.24      inference('sup-', [status(thm)], ['0', '5'])).
% 3.02/3.24  thf(t2_tarski, axiom,
% 3.02/3.24    (![A:$i,B:$i]:
% 3.02/3.24     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 3.02/3.24       ( ( A ) = ( B ) ) ))).
% 3.02/3.24  thf('28', plain,
% 3.02/3.24      (![X0 : $i, X1 : $i]:
% 3.02/3.24         (((X1) = (X0))
% 3.02/3.24          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 3.02/3.24          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 3.02/3.24      inference('cnf', [status(esa)], [t2_tarski])).
% 3.02/3.24  thf('29', plain,
% 3.02/3.24      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.02/3.24         (~ (r2_hidden @ X11 @ (k11_relat_1 @ X12 @ X13))
% 3.02/3.24          | (r2_hidden @ (k4_tarski @ X13 @ X11) @ X12)
% 3.02/3.24          | ~ (v1_relat_1 @ X12))),
% 3.02/3.24      inference('cnf', [status(esa)], [t204_relat_1])).
% 3.02/3.24  thf('30', plain,
% 3.02/3.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.02/3.24         ((r2_hidden @ (sk_C @ (k11_relat_1 @ X1 @ X0) @ X2) @ X2)
% 3.02/3.24          | ((X2) = (k11_relat_1 @ X1 @ X0))
% 3.02/3.24          | ~ (v1_relat_1 @ X1)
% 3.02/3.24          | (r2_hidden @ 
% 3.02/3.24             (k4_tarski @ X0 @ (sk_C @ (k11_relat_1 @ X1 @ X0) @ X2)) @ X1))),
% 3.02/3.24      inference('sup-', [status(thm)], ['28', '29'])).
% 3.02/3.24  thf('31', plain,
% 3.02/3.24      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 3.02/3.24         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6)
% 3.02/3.24          | (r2_hidden @ X4 @ X7)
% 3.02/3.24          | ((X7) != (k1_relat_1 @ X6)))),
% 3.02/3.24      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.02/3.24  thf('32', plain,
% 3.02/3.24      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.02/3.24         ((r2_hidden @ X4 @ (k1_relat_1 @ X6))
% 3.02/3.24          | ~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6))),
% 3.02/3.24      inference('simplify', [status(thm)], ['31'])).
% 3.02/3.24  thf('33', plain,
% 3.02/3.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.02/3.24         (~ (v1_relat_1 @ X0)
% 3.02/3.24          | ((X1) = (k11_relat_1 @ X0 @ X2))
% 3.02/3.24          | (r2_hidden @ (sk_C @ (k11_relat_1 @ X0 @ X2) @ X1) @ X1)
% 3.02/3.24          | (r2_hidden @ X2 @ (k1_relat_1 @ X0)))),
% 3.02/3.24      inference('sup-', [status(thm)], ['30', '32'])).
% 3.02/3.24  thf('34', plain,
% 3.02/3.24      (![X6 : $i, X9 : $i]:
% 3.02/3.24         (((X9) = (k1_relat_1 @ X6))
% 3.02/3.24          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X9 @ X6) @ (sk_D @ X9 @ X6)) @ 
% 3.02/3.24             X6)
% 3.02/3.24          | (r2_hidden @ (sk_C_1 @ X9 @ X6) @ X9))),
% 3.02/3.24      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.02/3.24  thf('35', plain,
% 3.02/3.24      (![X0 : $i]: (((k1_xboole_0) = (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 3.02/3.24      inference('sup-', [status(thm)], ['0', '5'])).
% 3.02/3.24  thf('36', plain,
% 3.02/3.24      (![X6 : $i, X8 : $i]:
% 3.02/3.24         ((r2_hidden @ (k4_tarski @ X8 @ (sk_D_1 @ X8 @ X6)) @ X6)
% 3.02/3.24          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X6)))),
% 3.02/3.24      inference('simplify', [status(thm)], ['13'])).
% 3.02/3.24  thf('37', plain,
% 3.02/3.24      (![X0 : $i, X1 : $i]:
% 3.02/3.24         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 3.02/3.24          | ~ (v1_xboole_0 @ X0)
% 3.02/3.24          | (r2_hidden @ (k4_tarski @ X1 @ (sk_D_1 @ X1 @ X0)) @ X0))),
% 3.02/3.24      inference('sup-', [status(thm)], ['35', '36'])).
% 3.02/3.24  thf('38', plain,
% 3.02/3.24      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 3.02/3.24      inference('cnf', [status(esa)], [t7_boole])).
% 3.02/3.24  thf('39', plain,
% 3.02/3.24      (![X0 : $i, X1 : $i]:
% 3.02/3.24         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 3.02/3.24      inference('clc', [status(thm)], ['37', '38'])).
% 3.02/3.24  thf('40', plain,
% 3.02/3.24      (![X0 : $i, X1 : $i]:
% 3.02/3.24         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 3.02/3.24          | ((X0) = (k1_relat_1 @ k1_xboole_0))
% 3.02/3.24          | ~ (v1_xboole_0 @ X1))),
% 3.02/3.24      inference('sup-', [status(thm)], ['34', '39'])).
% 3.02/3.24  thf('41', plain,
% 3.02/3.24      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 3.02/3.24      inference('cnf', [status(esa)], [t7_boole])).
% 3.02/3.24  thf('42', plain,
% 3.02/3.24      (![X0 : $i, X1 : $i]:
% 3.02/3.24         (~ (v1_xboole_0 @ X1)
% 3.02/3.24          | ((X0) = (k1_relat_1 @ k1_xboole_0))
% 3.02/3.24          | ~ (v1_xboole_0 @ X0))),
% 3.02/3.24      inference('sup-', [status(thm)], ['40', '41'])).
% 3.02/3.24  thf('43', plain,
% 3.02/3.24      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 3.02/3.24      inference('condensation', [status(thm)], ['42'])).
% 3.02/3.24  thf('44', plain,
% 3.02/3.24      (![X0 : $i, X1 : $i]:
% 3.02/3.24         (((X1) = (X0))
% 3.02/3.24          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 3.02/3.24          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 3.02/3.24      inference('cnf', [status(esa)], [t2_tarski])).
% 3.02/3.24  thf('45', plain,
% 3.02/3.24      (![X6 : $i, X8 : $i]:
% 3.02/3.24         ((r2_hidden @ (k4_tarski @ X8 @ (sk_D_1 @ X8 @ X6)) @ X6)
% 3.02/3.24          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X6)))),
% 3.02/3.24      inference('simplify', [status(thm)], ['13'])).
% 3.02/3.24  thf('46', plain,
% 3.02/3.24      (![X0 : $i, X1 : $i]:
% 3.02/3.24         ((r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X1)
% 3.02/3.24          | ((k1_relat_1 @ X0) = (X1))
% 3.02/3.24          | (r2_hidden @ 
% 3.02/3.24             (k4_tarski @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 3.02/3.24              (sk_D_1 @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 3.02/3.24             X0))),
% 3.02/3.24      inference('sup-', [status(thm)], ['44', '45'])).
% 3.02/3.24  thf('47', plain,
% 3.02/3.24      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 3.02/3.24      inference('cnf', [status(esa)], [t7_boole])).
% 3.02/3.24  thf('48', plain,
% 3.02/3.24      (![X0 : $i, X1 : $i]:
% 3.02/3.24         (((k1_relat_1 @ X0) = (X1))
% 3.02/3.24          | (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X1)
% 3.02/3.24          | ~ (v1_xboole_0 @ X0))),
% 3.02/3.24      inference('sup-', [status(thm)], ['46', '47'])).
% 3.02/3.24  thf('49', plain,
% 3.02/3.24      (![X0 : $i, X1 : $i]:
% 3.02/3.24         (((X1) = (X0))
% 3.02/3.24          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 3.02/3.24          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 3.02/3.24      inference('cnf', [status(esa)], [t2_tarski])).
% 3.02/3.24  thf('50', plain,
% 3.02/3.24      (![X0 : $i, X1 : $i]:
% 3.02/3.24         (~ (v1_xboole_0 @ X1)
% 3.02/3.24          | ((k1_relat_1 @ X1) = (X0))
% 3.02/3.24          | ~ (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ (k1_relat_1 @ X1))
% 3.02/3.24          | ((k1_relat_1 @ X1) = (X0)))),
% 3.02/3.24      inference('sup-', [status(thm)], ['48', '49'])).
% 3.02/3.24  thf('51', plain,
% 3.02/3.24      (![X0 : $i, X1 : $i]:
% 3.02/3.24         (~ (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ (k1_relat_1 @ X1))
% 3.02/3.24          | ((k1_relat_1 @ X1) = (X0))
% 3.02/3.24          | ~ (v1_xboole_0 @ X1))),
% 3.02/3.24      inference('simplify', [status(thm)], ['50'])).
% 3.02/3.24  thf('52', plain,
% 3.02/3.24      (![X0 : $i, X1 : $i]:
% 3.02/3.24         (~ (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ k1_xboole_0))
% 3.02/3.24          | ~ (v1_xboole_0 @ X0)
% 3.02/3.24          | ~ (v1_xboole_0 @ k1_xboole_0)
% 3.02/3.24          | ((k1_relat_1 @ k1_xboole_0) = (X1)))),
% 3.02/3.24      inference('sup-', [status(thm)], ['43', '51'])).
% 3.02/3.24  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.02/3.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.02/3.24  thf('54', plain,
% 3.02/3.24      (![X0 : $i, X1 : $i]:
% 3.02/3.24         (~ (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ k1_xboole_0))
% 3.02/3.24          | ~ (v1_xboole_0 @ X0)
% 3.02/3.24          | ((k1_relat_1 @ k1_xboole_0) = (X1)))),
% 3.02/3.24      inference('demod', [status(thm)], ['52', '53'])).
% 3.02/3.24  thf('55', plain,
% 3.02/3.24      (![X0 : $i, X1 : $i]:
% 3.02/3.24         ((r2_hidden @ X0 @ (k1_relat_1 @ X1))
% 3.02/3.24          | ((k1_relat_1 @ k1_xboole_0) = (k11_relat_1 @ X1 @ X0))
% 3.02/3.24          | ~ (v1_relat_1 @ X1)
% 3.02/3.24          | ((k1_relat_1 @ k1_xboole_0) = (k11_relat_1 @ X1 @ X0))
% 3.02/3.24          | ~ (v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0)))),
% 3.02/3.24      inference('sup-', [status(thm)], ['33', '54'])).
% 3.02/3.24  thf('56', plain,
% 3.02/3.24      (![X0 : $i, X1 : $i]:
% 3.02/3.24         (~ (v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 3.02/3.24          | ~ (v1_relat_1 @ X1)
% 3.02/3.24          | ((k1_relat_1 @ k1_xboole_0) = (k11_relat_1 @ X1 @ X0))
% 3.02/3.24          | (r2_hidden @ X0 @ (k1_relat_1 @ X1)))),
% 3.02/3.24      inference('simplify', [status(thm)], ['55'])).
% 3.02/3.24  thf('57', plain,
% 3.02/3.24      (![X0 : $i, X1 : $i]:
% 3.02/3.24         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.02/3.24          | ~ (v1_xboole_0 @ k1_xboole_0)
% 3.02/3.24          | (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 3.02/3.24          | ((k1_relat_1 @ k1_xboole_0) = (k11_relat_1 @ X0 @ X1))
% 3.02/3.24          | ~ (v1_relat_1 @ X0))),
% 3.02/3.24      inference('sup-', [status(thm)], ['27', '56'])).
% 3.02/3.24  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.02/3.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.02/3.24  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.02/3.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.02/3.24  thf('60', plain,
% 3.02/3.24      (![X0 : $i, X1 : $i]:
% 3.02/3.24         ((r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 3.02/3.24          | ((k1_relat_1 @ k1_xboole_0) = (k11_relat_1 @ X0 @ X1))
% 3.02/3.24          | ~ (v1_relat_1 @ X0))),
% 3.02/3.24      inference('demod', [status(thm)], ['57', '58', '59'])).
% 3.02/3.24  thf('61', plain,
% 3.02/3.24      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 3.02/3.24         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 3.02/3.24      inference('split', [status(esa)], ['10'])).
% 3.02/3.24  thf('62', plain,
% 3.02/3.24      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 3.02/3.24       (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 3.02/3.24      inference('split', [status(esa)], ['10'])).
% 3.02/3.24  thf('63', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 3.02/3.24      inference('sat_resolution*', [status(thm)], ['9', '24', '62'])).
% 3.02/3.24  thf('64', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 3.02/3.24      inference('simpl_trail', [status(thm)], ['61', '63'])).
% 3.02/3.24  thf('65', plain,
% 3.02/3.24      ((~ (v1_relat_1 @ sk_B)
% 3.02/3.24        | ((k1_relat_1 @ k1_xboole_0) = (k11_relat_1 @ sk_B @ sk_A)))),
% 3.02/3.24      inference('sup-', [status(thm)], ['60', '64'])).
% 3.02/3.24  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 3.02/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.02/3.24  thf('67', plain,
% 3.02/3.24      (((k1_relat_1 @ k1_xboole_0) = (k11_relat_1 @ sk_B @ sk_A))),
% 3.02/3.24      inference('demod', [status(thm)], ['65', '66'])).
% 3.02/3.24  thf('68', plain, (((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 3.02/3.24      inference('demod', [status(thm)], ['26', '67'])).
% 3.02/3.24  thf('69', plain,
% 3.02/3.24      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.02/3.24      inference('sup-', [status(thm)], ['6', '68'])).
% 3.02/3.24  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.02/3.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.02/3.24  thf('71', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 3.02/3.24      inference('demod', [status(thm)], ['69', '70'])).
% 3.02/3.24  thf('72', plain, ($false), inference('simplify', [status(thm)], ['71'])).
% 3.02/3.24  
% 3.02/3.24  % SZS output end Refutation
% 3.02/3.24  
% 3.02/3.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

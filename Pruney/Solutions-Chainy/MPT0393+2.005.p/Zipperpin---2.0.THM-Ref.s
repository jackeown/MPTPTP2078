%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FGlP2ETsEr

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:41 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 558 expanded)
%              Number of leaves         :   23 ( 165 expanded)
%              Depth                    :   31
%              Number of atoms          :  888 (5044 expanded)
%              Number of equality atoms :   92 ( 443 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X44: $i,X45: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X45 @ X44 ) @ X44 )
      | ( r1_tarski @ X45 @ ( k1_setfam_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ( X28 = X25 )
      | ( X27
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X25: $i,X28: $i] :
      ( ( X28 = X25 )
      | ~ ( r2_hidden @ X28 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X26 != X25 )
      | ( r2_hidden @ X26 @ X27 )
      | ( X27
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X25: $i] :
      ( r2_hidden @ X25 @ ( k1_tarski @ X25 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X25: $i,X28: $i] :
      ( ( X28 = X25 )
      | ~ ( r2_hidden @ X28 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('16',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['16'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('19',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_tarski @ X37 @ ( k1_tarski @ X38 ) )
      | ( X37 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('20',plain,(
    ! [X38: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X38 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X25: $i,X28: $i] :
      ( ( X28 = X25 )
      | ~ ( r2_hidden @ X28 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( ( sk_C @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ k1_xboole_0 )
       != sk_A )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( ( sk_C @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','31'])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('34',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X2 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','31'])).

thf('37',plain,(
    ! [X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X2 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('38',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( ( k4_xboole_0 @ X41 @ ( k1_tarski @ X40 ) )
       != X41 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['14','41'])).

thf('43',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('45',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X36: $i,X37: $i] :
      ( ( X37
        = ( k1_tarski @ X36 ) )
      | ( X37 = k1_xboole_0 )
      | ~ ( r1_tarski @ X37 @ ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('53',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','40'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X2 @ X2 ) @ X1 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X2 @ X2 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(clc,[status(thm)],['59','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','62'])).

thf('64',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('65',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( ( k4_xboole_0 @ X41 @ ( k1_tarski @ X40 ) )
       != X41 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
       != X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X25: $i] :
      ( r2_hidden @ X25 @ ( k1_tarski @ X25 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('69',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['4','69'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('71',plain,(
    ! [X39: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf(t3_setfam_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ) )).

thf('72',plain,(
    ! [X43: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ X43 ) @ ( k3_tarski @ X43 ) ) ),
    inference(cnf,[status(esa)],[t3_setfam_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('74',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ X0 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X44: $i,X45: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( r1_tarski @ X45 @ ( sk_C_2 @ X45 @ X44 ) )
      | ( r1_tarski @ X45 @ ( k1_setfam_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('80',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['78','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('85',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','85'])).

thf('87',plain,(
    $false ),
    inference(simplify,[status(thm)],['86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FGlP2ETsEr
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:13:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 251 iterations in 0.175s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.46/0.64  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.64  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.46/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.64  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(t11_setfam_1, conjecture,
% 0.46/0.64    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 0.46/0.64  thf('0', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t6_setfam_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.46/0.64       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X44 : $i, X45 : $i]:
% 0.46/0.64         (((X44) = (k1_xboole_0))
% 0.46/0.64          | (r2_hidden @ (sk_C_2 @ X45 @ X44) @ X44)
% 0.46/0.64          | (r1_tarski @ X45 @ (k1_setfam_1 @ X44)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.46/0.64  thf(d1_tarski, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.46/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X28 @ X27)
% 0.46/0.64          | ((X28) = (X25))
% 0.46/0.64          | ((X27) != (k1_tarski @ X25)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_tarski])).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X25 : $i, X28 : $i]:
% 0.46/0.64         (((X28) = (X25)) | ~ (r2_hidden @ X28 @ (k1_tarski @ X25)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['2'])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.46/0.64          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.64          | ((sk_C_2 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['1', '3'])).
% 0.46/0.64  thf(t69_enumset1, axiom,
% 0.46/0.64    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.64  thf('5', plain, (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 0.46/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.64         (((X26) != (X25))
% 0.46/0.64          | (r2_hidden @ X26 @ X27)
% 0.46/0.64          | ((X27) != (k1_tarski @ X25)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_tarski])).
% 0.46/0.64  thf('7', plain, (![X25 : $i]: (r2_hidden @ X25 @ (k1_tarski @ X25))),
% 0.46/0.64      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.64  thf('8', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['5', '7'])).
% 0.46/0.64  thf(d5_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.46/0.64       ( ![D:$i]:
% 0.46/0.64         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.64           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.46/0.64         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.46/0.64          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.46/0.64          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.46/0.64         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.46/0.64          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.46/0.64          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.46/0.64          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.46/0.64          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.46/0.64          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.46/0.64          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.46/0.64      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X25 : $i, X28 : $i]:
% 0.46/0.64         (((X28) = (X25)) | ~ (r2_hidden @ X28 @ (k1_tarski @ X25)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['2'])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 0.46/0.64          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['12', '13'])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.46/0.64          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.46/0.64      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.46/0.64         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.46/0.64          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.46/0.64          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.46/0.64          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.64      inference('eq_fact', [status(thm)], ['16'])).
% 0.46/0.64  thf(d3_tarski, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X1 : $i, X3 : $i]:
% 0.46/0.64         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf(l3_zfmisc_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.46/0.64       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (![X37 : $i, X38 : $i]:
% 0.46/0.64         ((r1_tarski @ X37 @ (k1_tarski @ X38)) | ((X37) != (k1_xboole_0)))),
% 0.46/0.64      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X38 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X38))),
% 0.46/0.64      inference('simplify', [status(thm)], ['19'])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.64          | (r2_hidden @ X0 @ X2)
% 0.46/0.64          | ~ (r1_tarski @ X1 @ X2))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.46/0.64          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r1_tarski @ k1_xboole_0 @ X0)
% 0.46/0.64          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ (k1_tarski @ X1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['18', '22'])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X25 : $i, X28 : $i]:
% 0.46/0.64         (((X28) = (X25)) | ~ (r2_hidden @ X28 @ (k1_tarski @ X25)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['2'])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r1_tarski @ k1_xboole_0 @ X1) | ((sk_C @ X1 @ k1_xboole_0) = (X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.64  thf('26', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((sk_C @ X0 @ k1_xboole_0) != (sk_A))
% 0.46/0.64          | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r1_tarski @ k1_xboole_0 @ X1) | ((sk_C @ X1 @ k1_xboole_0) = (X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.64  thf('29', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.46/0.64      inference('clc', [status(thm)], ['27', '28'])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.64          | (r2_hidden @ X0 @ X2)
% 0.46/0.64          | ~ (r1_tarski @ X1 @ X2))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.46/0.64          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['17', '31'])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X8 @ X7)
% 0.46/0.64          | ~ (r2_hidden @ X8 @ X6)
% 0.46/0.64          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X8 @ X6)
% 0.46/0.64          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['33'])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X0 : $i, X2 : $i]:
% 0.46/0.64         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X2))
% 0.46/0.64          | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ X2 @ k1_xboole_0) @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['32', '34'])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.46/0.64          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['17', '31'])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      (![X2 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X2))),
% 0.46/0.64      inference('clc', [status(thm)], ['35', '36'])).
% 0.46/0.64  thf(t65_zfmisc_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.46/0.64       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X40 : $i, X41 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X40 @ X41)
% 0.46/0.64          | ((k4_xboole_0 @ X41 @ (k1_tarski @ X40)) != (X41)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.64  thf('40', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.46/0.64      inference('simplify', [status(thm)], ['39'])).
% 0.46/0.64  thf('41', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['15', '40'])).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.64          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['14', '41'])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      (![X1 : $i, X3 : $i]:
% 0.46/0.64         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X8 @ X7)
% 0.46/0.64          | (r2_hidden @ X8 @ X5)
% 0.46/0.64          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.46/0.64         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['44'])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.46/0.64          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['43', '45'])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      (![X1 : $i, X3 : $i]:
% 0.46/0.64         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.46/0.64          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['46', '47'])).
% 0.46/0.64  thf('49', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.46/0.64      inference('simplify', [status(thm)], ['48'])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      (![X36 : $i, X37 : $i]:
% 0.46/0.64         (((X37) = (k1_tarski @ X36))
% 0.46/0.64          | ((X37) = (k1_xboole_0))
% 0.46/0.64          | ~ (r1_tarski @ X37 @ (k1_tarski @ X36)))),
% 0.46/0.64      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.46/0.64          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['49', '50'])).
% 0.46/0.64  thf('52', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.46/0.64          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.46/0.64      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.64  thf('53', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['15', '40'])).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.46/0.64      inference('demod', [status(thm)], ['52', '53'])).
% 0.46/0.64  thf('55', plain,
% 0.46/0.64      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X8 @ X6)
% 0.46/0.64          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['33'])).
% 0.46/0.64  thf('56', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.46/0.64          | ~ (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.64  thf('57', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X2 @ X2) @ X1)
% 0.46/0.64          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.46/0.64          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['51', '56'])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.46/0.64          | ~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X2 @ X2) @ X1))),
% 0.46/0.64      inference('simplify', [status(thm)], ['57'])).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.64          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.64          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['42', '58'])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.46/0.64          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['49', '50'])).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k1_tarski @ X0) != (k1_xboole_0))
% 0.46/0.64          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.46/0.64      inference('eq_fact', [status(thm)], ['60'])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.46/0.64          | ~ (r2_hidden @ X0 @ X1))),
% 0.46/0.64      inference('clc', [status(thm)], ['59', '61'])).
% 0.46/0.64  thf('63', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))
% 0.46/0.64           = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['8', '62'])).
% 0.46/0.64  thf('64', plain,
% 0.46/0.64      (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 0.46/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.64  thf('65', plain,
% 0.46/0.64      (![X40 : $i, X41 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X40 @ X41)
% 0.46/0.64          | ((k4_xboole_0 @ X41 @ (k1_tarski @ X40)) != (X41)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.46/0.64  thf('66', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)) != (X1))
% 0.46/0.64          | ~ (r2_hidden @ X0 @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['64', '65'])).
% 0.46/0.64  thf('67', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.46/0.64          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['63', '66'])).
% 0.46/0.64  thf('68', plain, (![X25 : $i]: (r2_hidden @ X25 @ (k1_tarski @ X25))),
% 0.46/0.64      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.64  thf('69', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['67', '68'])).
% 0.46/0.64  thf('70', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((sk_C_2 @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.46/0.64          | (r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.46/0.64      inference('clc', [status(thm)], ['4', '69'])).
% 0.46/0.64  thf(t31_zfmisc_1, axiom,
% 0.46/0.64    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.46/0.64  thf('71', plain, (![X39 : $i]: ((k3_tarski @ (k1_tarski @ X39)) = (X39))),
% 0.46/0.64      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.46/0.64  thf(t3_setfam_1, axiom,
% 0.46/0.64    (![A:$i]: ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ))).
% 0.46/0.64  thf('72', plain,
% 0.46/0.64      (![X43 : $i]: (r1_tarski @ (k1_setfam_1 @ X43) @ (k3_tarski @ X43))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_setfam_1])).
% 0.46/0.64  thf('73', plain,
% 0.46/0.64      (![X0 : $i]: (r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X0)),
% 0.46/0.64      inference('sup+', [status(thm)], ['71', '72'])).
% 0.46/0.64  thf(d10_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.64  thf('74', plain,
% 0.46/0.64      (![X10 : $i, X12 : $i]:
% 0.46/0.64         (((X10) = (X12))
% 0.46/0.64          | ~ (r1_tarski @ X12 @ X10)
% 0.46/0.64          | ~ (r1_tarski @ X10 @ X12))),
% 0.46/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.64  thf('75', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.46/0.64          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['73', '74'])).
% 0.46/0.64  thf('76', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((sk_C_2 @ X0 @ (k1_tarski @ X0)) = (X0))
% 0.46/0.64          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['70', '75'])).
% 0.46/0.64  thf('77', plain,
% 0.46/0.64      (![X44 : $i, X45 : $i]:
% 0.46/0.64         (((X44) = (k1_xboole_0))
% 0.46/0.64          | ~ (r1_tarski @ X45 @ (sk_C_2 @ X45 @ X44))
% 0.46/0.64          | (r1_tarski @ X45 @ (k1_setfam_1 @ X44)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.46/0.64  thf('78', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X0 @ X0)
% 0.46/0.64          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.46/0.64          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.46/0.64          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['76', '77'])).
% 0.46/0.64  thf('79', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.64  thf('80', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.46/0.64      inference('simplify', [status(thm)], ['79'])).
% 0.46/0.64  thf('81', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.46/0.64          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.46/0.64          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['78', '80'])).
% 0.46/0.64  thf('82', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.46/0.64          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['73', '74'])).
% 0.46/0.64  thf('83', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.64          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.46/0.64      inference('clc', [status(thm)], ['81', '82'])).
% 0.46/0.64  thf('84', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['67', '68'])).
% 0.46/0.64  thf('85', plain, (![X0 : $i]: ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))),
% 0.46/0.64      inference('clc', [status(thm)], ['83', '84'])).
% 0.46/0.64  thf('86', plain, (((sk_A) != (sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['0', '85'])).
% 0.46/0.64  thf('87', plain, ($false), inference('simplify', [status(thm)], ['86'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

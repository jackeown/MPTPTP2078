%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0720+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2zOrw5Hpfl

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:23 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 151 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :   21
%              Number of atoms          :  803 (1707 expanded)
%              Number of equality atoms :   31 (  56 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ ( k1_relat_1 @ X8 ) )
      | ( X9 = k1_xboole_0 )
      | ( X9
       != ( k1_funct_1 @ X8 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( ( k1_funct_1 @ X8 @ X7 )
        = k1_xboole_0 )
      | ( r2_hidden @ X7 @ ( k1_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_C_1 @ ( k1_relat_1 @ X0 ) @ X1 ) )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t175_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B )
            & ( v5_funct_1 @ B @ A ) )
         => ( r1_tarski @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B )
              & ( v5_funct_1 @ B @ A ) )
           => ( r1_tarski @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_1])).

thf('4',plain,(
    v5_funct_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C_1 @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d20_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( v5_funct_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
               => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v5_funct_1 @ X0 @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X2 ) @ ( k1_funct_1 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k1_funct_1 @ X2 @ ( sk_C_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v5_funct_1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) ) @ ( k1_funct_1 @ sk_A @ ( sk_C_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) ) @ ( k1_funct_1 @ sk_A @ ( sk_C_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C_1 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) @ k1_xboole_0 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_C_1 @ ( k1_relat_1 @ X0 ) @ X1 ) )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('16',plain,(
    v5_funct_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( ( k1_funct_1 @ X8 @ X7 )
        = k1_xboole_0 )
      | ( r2_hidden @ X7 @ ( k1_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v5_funct_1 @ X0 @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X2 ) @ ( k1_funct_1 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ ( k1_funct_1 @ X2 @ X1 ) )
      | ~ ( v5_funct_1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v5_funct_1 @ X0 @ X2 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ ( k1_funct_1 @ X2 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k1_funct_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k1_funct_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k1_funct_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','28'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('30',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('31',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('33',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_A ) )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','34','35','36'])).

thf('38',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C_1 @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X10 ) @ X8 )
      | ( X10
       != ( k1_funct_1 @ X8 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ ( k1_funct_1 @ X8 @ X7 ) ) @ X8 )
      | ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 ) @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 ) @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 ) @ sk_B ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 ) @ sk_B ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( ( k1_funct_1 @ X8 @ X7 )
        = k1_xboole_0 )
      | ( r2_hidden @ X7 @ ( k1_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('50',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X8 ) )
      | ( X10
        = ( k1_funct_1 @ X8 @ X7 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X10 ) @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( X2
        = ( k1_funct_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_B @ ( sk_C_1 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
      = k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_B @ ( sk_C_1 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','57','58','59'])).

thf('61',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    r2_hidden @ k1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('65',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','33'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['65','66'])).


%------------------------------------------------------------------------------

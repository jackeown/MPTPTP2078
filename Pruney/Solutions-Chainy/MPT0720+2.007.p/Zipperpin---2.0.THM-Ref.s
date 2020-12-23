%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Tj0VGHicK5

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:35 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 337 expanded)
%              Number of leaves         :   20 ( 106 expanded)
%              Depth                    :   22
%              Number of atoms          : 1008 (4417 expanded)
%              Number of equality atoms :   31 ( 124 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( X14 = k1_xboole_0 )
      | ( X14
       != ( k1_funct_1 @ X13 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( ( k1_funct_1 @ X13 @ X12 )
        = k1_xboole_0 )
      | ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_C @ ( k1_relat_1 @ X0 ) @ X1 ) )
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
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v5_funct_1 @ X9 @ X10 )
      | ( r2_hidden @ ( k1_funct_1 @ X9 @ X11 ) @ ( k1_funct_1 @ X10 @ X11 ) )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k1_funct_1 @ X2 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v5_funct_1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) ) )
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
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) @ k1_xboole_0 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_C @ ( k1_relat_1 @ X0 ) @ X1 ) )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('16',plain,(
    v5_funct_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( ( k1_funct_1 @ X13 @ X12 )
        = k1_xboole_0 )
      | ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v5_funct_1 @ X9 @ X10 )
      | ( r2_hidden @ ( k1_funct_1 @ X9 @ X11 ) @ ( k1_funct_1 @ X10 @ X11 ) )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ X0 ) ) @ k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ X0 ) ) @ k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_A ) )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('31',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k1_funct_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

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

thf('33',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k1_funct_1 @ sk_A @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ k1_xboole_0 )
      | ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X15 ) @ X13 )
      | ( X15
       != ( k1_funct_1 @ X13 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ ( k1_funct_1 @ X13 @ X12 ) ) @ X13 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 ) @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['36','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 ) @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 ) @ sk_B ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 ) @ sk_B ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( ( k1_funct_1 @ X13 @ X12 )
        = k1_xboole_0 )
      | ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('49',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( X15
        = ( k1_funct_1 @ X13 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X15 ) @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('50',plain,(
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
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
      = k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','56','57','58'])).

thf('60',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    r2_hidden @ k1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    r2_hidden @ k1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['60','61'])).

thf('64',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('67',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('68',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('69',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('70',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('71',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['67','77'])).

thf('79',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('80',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['66','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['65','84'])).

thf('86',plain,(
    $false ),
    inference('sup-',[status(thm)],['62','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Tj0VGHicK5
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:04:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 134 iterations in 0.082s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.58  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.38/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.58  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.38/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.58  thf(d4_funct_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.58       ( ![B:$i,C:$i]:
% 0.38/0.58         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.38/0.58             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.38/0.58               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.58           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.38/0.58             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.38/0.58               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.38/0.58  thf('0', plain,
% 0.38/0.58      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.58         ((r2_hidden @ X12 @ (k1_relat_1 @ X13))
% 0.38/0.58          | ((X14) = (k1_xboole_0))
% 0.38/0.58          | ((X14) != (k1_funct_1 @ X13 @ X12))
% 0.38/0.58          | ~ (v1_funct_1 @ X13)
% 0.38/0.58          | ~ (v1_relat_1 @ X13))),
% 0.38/0.58      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.38/0.58  thf('1', plain,
% 0.38/0.58      (![X12 : $i, X13 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X13)
% 0.38/0.58          | ~ (v1_funct_1 @ X13)
% 0.38/0.58          | ((k1_funct_1 @ X13 @ X12) = (k1_xboole_0))
% 0.38/0.58          | (r2_hidden @ X12 @ (k1_relat_1 @ X13)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.58  thf(d3_tarski, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.58  thf('2', plain,
% 0.38/0.58      (![X1 : $i, X3 : $i]:
% 0.38/0.58         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.38/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (((k1_funct_1 @ X0 @ (sk_C @ (k1_relat_1 @ X0) @ X1)) = (k1_xboole_0))
% 0.38/0.58          | ~ (v1_funct_1 @ X0)
% 0.38/0.58          | ~ (v1_relat_1 @ X0)
% 0.38/0.58          | (r1_tarski @ X1 @ (k1_relat_1 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.58  thf(t175_funct_1, conjecture,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) & ( v5_funct_1 @ B @ A ) ) =>
% 0.38/0.58           ( r1_tarski @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i]:
% 0.38/0.58        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.58          ( ![B:$i]:
% 0.38/0.58            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) & 
% 0.38/0.58                ( v5_funct_1 @ B @ A ) ) =>
% 0.38/0.58              ( r1_tarski @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t175_funct_1])).
% 0.38/0.58  thf('4', plain, ((v5_funct_1 @ sk_B @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('5', plain,
% 0.38/0.58      (![X1 : $i, X3 : $i]:
% 0.38/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.58  thf(d20_funct_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.58           ( ( v5_funct_1 @ B @ A ) <=>
% 0.38/0.58             ( ![C:$i]:
% 0.38/0.58               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.38/0.58                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf('6', plain,
% 0.38/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X9)
% 0.38/0.58          | ~ (v1_funct_1 @ X9)
% 0.38/0.58          | ~ (v5_funct_1 @ X9 @ X10)
% 0.38/0.58          | (r2_hidden @ (k1_funct_1 @ X9 @ X11) @ (k1_funct_1 @ X10 @ X11))
% 0.38/0.58          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X9))
% 0.38/0.58          | ~ (v1_funct_1 @ X10)
% 0.38/0.58          | ~ (v1_relat_1 @ X10))),
% 0.38/0.58      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.38/0.58  thf('7', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.38/0.58          | ~ (v1_relat_1 @ X2)
% 0.38/0.58          | ~ (v1_funct_1 @ X2)
% 0.38/0.58          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_C @ X1 @ (k1_relat_1 @ X0))) @ 
% 0.38/0.58             (k1_funct_1 @ X2 @ (sk_C @ X1 @ (k1_relat_1 @ X0))))
% 0.38/0.58          | ~ (v5_funct_1 @ X0 @ X2)
% 0.38/0.58          | ~ (v1_funct_1 @ X0)
% 0.38/0.58          | ~ (v1_relat_1 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ sk_B)
% 0.38/0.58          | ~ (v1_funct_1 @ sk_B)
% 0.38/0.58          | (r2_hidden @ 
% 0.38/0.58             (k1_funct_1 @ sk_B @ (sk_C @ X0 @ (k1_relat_1 @ sk_B))) @ 
% 0.38/0.58             (k1_funct_1 @ sk_A @ (sk_C @ X0 @ (k1_relat_1 @ sk_B))))
% 0.38/0.58          | ~ (v1_funct_1 @ sk_A)
% 0.38/0.58          | ~ (v1_relat_1 @ sk_A)
% 0.38/0.58          | (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['4', '7'])).
% 0.38/0.58  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('10', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('11', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('13', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((r2_hidden @ 
% 0.38/0.58           (k1_funct_1 @ sk_B @ (sk_C @ X0 @ (k1_relat_1 @ sk_B))) @ 
% 0.38/0.58           (k1_funct_1 @ sk_A @ (sk_C @ X0 @ (k1_relat_1 @ sk_B))))
% 0.38/0.58          | (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.38/0.58  thf('14', plain,
% 0.38/0.58      (((r2_hidden @ 
% 0.38/0.58         (k1_funct_1 @ sk_B @ 
% 0.38/0.58          (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))) @ 
% 0.38/0.58         k1_xboole_0)
% 0.38/0.58        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.38/0.58        | ~ (v1_relat_1 @ sk_A)
% 0.38/0.58        | ~ (v1_funct_1 @ sk_A)
% 0.38/0.58        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['3', '13'])).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (((k1_funct_1 @ X0 @ (sk_C @ (k1_relat_1 @ X0) @ X1)) = (k1_xboole_0))
% 0.38/0.58          | ~ (v1_funct_1 @ X0)
% 0.38/0.58          | ~ (v1_relat_1 @ X0)
% 0.38/0.58          | (r1_tarski @ X1 @ (k1_relat_1 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.58  thf('16', plain, ((v5_funct_1 @ sk_B @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      (![X12 : $i, X13 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X13)
% 0.38/0.58          | ~ (v1_funct_1 @ X13)
% 0.38/0.58          | ((k1_funct_1 @ X13 @ X12) = (k1_xboole_0))
% 0.38/0.58          | (r2_hidden @ X12 @ (k1_relat_1 @ X13)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X9)
% 0.38/0.58          | ~ (v1_funct_1 @ X9)
% 0.38/0.58          | ~ (v5_funct_1 @ X9 @ X10)
% 0.38/0.58          | (r2_hidden @ (k1_funct_1 @ X9 @ X11) @ (k1_funct_1 @ X10 @ X11))
% 0.38/0.58          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X9))
% 0.38/0.58          | ~ (v1_funct_1 @ X10)
% 0.38/0.58          | ~ (v1_relat_1 @ X10))),
% 0.38/0.58      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.38/0.58          | ~ (v1_funct_1 @ X0)
% 0.38/0.58          | ~ (v1_relat_1 @ X0)
% 0.38/0.58          | ~ (v1_relat_1 @ X2)
% 0.38/0.58          | ~ (v1_funct_1 @ X2)
% 0.38/0.58          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ (k1_funct_1 @ X2 @ X1))
% 0.38/0.58          | ~ (v5_funct_1 @ X0 @ X2)
% 0.38/0.58          | ~ (v1_funct_1 @ X0)
% 0.38/0.58          | ~ (v1_relat_1 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.58  thf('20', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         (~ (v5_funct_1 @ X0 @ X2)
% 0.38/0.58          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ (k1_funct_1 @ X2 @ X1))
% 0.38/0.58          | ~ (v1_funct_1 @ X2)
% 0.38/0.58          | ~ (v1_relat_1 @ X2)
% 0.38/0.58          | ~ (v1_relat_1 @ X0)
% 0.38/0.58          | ~ (v1_funct_1 @ X0)
% 0.38/0.58          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['19'])).
% 0.38/0.58  thf('21', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.38/0.58          | ~ (v1_funct_1 @ sk_B)
% 0.38/0.58          | ~ (v1_relat_1 @ sk_B)
% 0.38/0.58          | ~ (v1_relat_1 @ sk_A)
% 0.38/0.58          | ~ (v1_funct_1 @ sk_A)
% 0.38/0.58          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k1_funct_1 @ sk_A @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['16', '20'])).
% 0.38/0.58  thf('22', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('25', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('26', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.38/0.58          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k1_funct_1 @ sk_A @ X0)))),
% 0.38/0.58      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.38/0.58  thf('27', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((r2_hidden @ 
% 0.38/0.58           (k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0)) @ 
% 0.38/0.58           k1_xboole_0)
% 0.38/0.58          | (r1_tarski @ X0 @ (k1_relat_1 @ sk_A))
% 0.38/0.58          | ~ (v1_relat_1 @ sk_A)
% 0.38/0.58          | ~ (v1_funct_1 @ sk_A)
% 0.38/0.58          | ((k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0))
% 0.38/0.58              = (k1_xboole_0)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['15', '26'])).
% 0.38/0.58  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('29', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('30', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((r2_hidden @ 
% 0.38/0.58           (k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0)) @ 
% 0.38/0.58           k1_xboole_0)
% 0.38/0.58          | (r1_tarski @ X0 @ (k1_relat_1 @ sk_A))
% 0.38/0.58          | ((k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0))
% 0.38/0.58              = (k1_xboole_0)))),
% 0.38/0.58      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.38/0.58  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.38/0.58  thf('31', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.38/0.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.38/0.58  thf('32', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.38/0.58          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k1_funct_1 @ sk_A @ X0)))),
% 0.38/0.58      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.38/0.58  thf(t3_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.38/0.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.38/0.58            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.38/0.58  thf('33', plain,
% 0.38/0.58      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X6 @ X4)
% 0.38/0.58          | ~ (r2_hidden @ X6 @ X7)
% 0.38/0.58          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.38/0.58  thf('34', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.38/0.58          | ~ (r1_xboole_0 @ (k1_funct_1 @ sk_A @ X0) @ X1)
% 0.38/0.58          | ~ (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ X1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.58  thf('35', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ k1_xboole_0)
% 0.38/0.58          | ((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['31', '34'])).
% 0.38/0.58  thf('36', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0))
% 0.38/0.58            = (k1_xboole_0))
% 0.38/0.58          | (r1_tarski @ X0 @ (k1_relat_1 @ sk_A)))),
% 0.38/0.58      inference('clc', [status(thm)], ['30', '35'])).
% 0.38/0.58  thf('37', plain,
% 0.38/0.58      (![X1 : $i, X3 : $i]:
% 0.38/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.58  thf('38', plain,
% 0.38/0.58      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X12 @ (k1_relat_1 @ X13))
% 0.38/0.58          | (r2_hidden @ (k4_tarski @ X12 @ X15) @ X13)
% 0.38/0.58          | ((X15) != (k1_funct_1 @ X13 @ X12))
% 0.38/0.58          | ~ (v1_funct_1 @ X13)
% 0.38/0.58          | ~ (v1_relat_1 @ X13))),
% 0.38/0.58      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.38/0.58  thf('39', plain,
% 0.38/0.58      (![X12 : $i, X13 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X13)
% 0.38/0.58          | ~ (v1_funct_1 @ X13)
% 0.38/0.58          | (r2_hidden @ (k4_tarski @ X12 @ (k1_funct_1 @ X13 @ X12)) @ X13)
% 0.38/0.58          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X13)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['38'])).
% 0.38/0.58  thf('40', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.38/0.58          | (r2_hidden @ 
% 0.38/0.58             (k4_tarski @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.38/0.58              (k1_funct_1 @ X0 @ (sk_C @ X1 @ (k1_relat_1 @ X0)))) @ 
% 0.38/0.58             X0)
% 0.38/0.58          | ~ (v1_funct_1 @ X0)
% 0.38/0.58          | ~ (v1_relat_1 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['37', '39'])).
% 0.38/0.58  thf('41', plain,
% 0.38/0.58      (((r2_hidden @ 
% 0.38/0.58         (k4_tarski @ (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) @ 
% 0.38/0.58          k1_xboole_0) @ 
% 0.38/0.58         sk_B)
% 0.38/0.58        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.38/0.58        | ~ (v1_relat_1 @ sk_B)
% 0.38/0.58        | ~ (v1_funct_1 @ sk_B)
% 0.38/0.58        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['36', '40'])).
% 0.38/0.58  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('43', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('44', plain,
% 0.38/0.58      (((r2_hidden @ 
% 0.38/0.58         (k4_tarski @ (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) @ 
% 0.38/0.58          k1_xboole_0) @ 
% 0.38/0.58         sk_B)
% 0.38/0.58        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.38/0.58        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A)))),
% 0.38/0.58      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.38/0.58  thf('45', plain,
% 0.38/0.58      (((r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.38/0.58        | (r2_hidden @ 
% 0.38/0.58           (k4_tarski @ (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) @ 
% 0.38/0.58            k1_xboole_0) @ 
% 0.38/0.58           sk_B))),
% 0.38/0.58      inference('simplify', [status(thm)], ['44'])).
% 0.38/0.58  thf('46', plain, (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('47', plain,
% 0.38/0.58      ((r2_hidden @ 
% 0.38/0.58        (k4_tarski @ (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) @ 
% 0.38/0.58         k1_xboole_0) @ 
% 0.38/0.58        sk_B)),
% 0.38/0.58      inference('clc', [status(thm)], ['45', '46'])).
% 0.38/0.58  thf('48', plain,
% 0.38/0.58      (![X12 : $i, X13 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X13)
% 0.38/0.58          | ~ (v1_funct_1 @ X13)
% 0.38/0.58          | ((k1_funct_1 @ X13 @ X12) = (k1_xboole_0))
% 0.38/0.58          | (r2_hidden @ X12 @ (k1_relat_1 @ X13)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['0'])).
% 0.38/0.58  thf('49', plain,
% 0.38/0.58      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X12 @ (k1_relat_1 @ X13))
% 0.38/0.58          | ((X15) = (k1_funct_1 @ X13 @ X12))
% 0.38/0.58          | ~ (r2_hidden @ (k4_tarski @ X12 @ X15) @ X13)
% 0.38/0.58          | ~ (v1_funct_1 @ X13)
% 0.38/0.58          | ~ (v1_relat_1 @ X13))),
% 0.38/0.58      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.38/0.58  thf('50', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.38/0.58          | ~ (v1_funct_1 @ X0)
% 0.38/0.58          | ~ (v1_relat_1 @ X0)
% 0.38/0.58          | ~ (v1_relat_1 @ X0)
% 0.38/0.58          | ~ (v1_funct_1 @ X0)
% 0.38/0.58          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.38/0.58          | ((X2) = (k1_funct_1 @ X0 @ X1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['48', '49'])).
% 0.38/0.58  thf('51', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         (((X2) = (k1_funct_1 @ X0 @ X1))
% 0.38/0.58          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.38/0.58          | ~ (v1_relat_1 @ X0)
% 0.38/0.58          | ~ (v1_funct_1 @ X0)
% 0.38/0.58          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['50'])).
% 0.38/0.58  thf('52', plain,
% 0.38/0.58      ((((k1_funct_1 @ sk_B @ 
% 0.38/0.58          (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))) = (k1_xboole_0))
% 0.38/0.58        | ~ (v1_funct_1 @ sk_B)
% 0.38/0.58        | ~ (v1_relat_1 @ sk_B)
% 0.38/0.58        | ((k1_xboole_0)
% 0.38/0.58            = (k1_funct_1 @ sk_B @ 
% 0.38/0.58               (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['47', '51'])).
% 0.38/0.58  thf('53', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('54', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('55', plain,
% 0.38/0.58      ((((k1_funct_1 @ sk_B @ 
% 0.38/0.58          (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))) = (k1_xboole_0))
% 0.38/0.58        | ((k1_xboole_0)
% 0.38/0.58            = (k1_funct_1 @ sk_B @ 
% 0.38/0.58               (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))))),
% 0.38/0.58      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.38/0.58  thf('56', plain,
% 0.38/0.58      (((k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))
% 0.38/0.58         = (k1_xboole_0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['55'])).
% 0.38/0.58  thf('57', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('58', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('59', plain,
% 0.38/0.58      (((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.38/0.58        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.38/0.58        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A)))),
% 0.38/0.58      inference('demod', [status(thm)], ['14', '56', '57', '58'])).
% 0.38/0.58  thf('60', plain,
% 0.38/0.58      (((r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.38/0.58        | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['59'])).
% 0.38/0.58  thf('61', plain, (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('62', plain, ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)),
% 0.38/0.58      inference('clc', [status(thm)], ['60', '61'])).
% 0.38/0.58  thf('63', plain, ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)),
% 0.38/0.58      inference('clc', [status(thm)], ['60', '61'])).
% 0.38/0.58  thf('64', plain,
% 0.38/0.58      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X6 @ X4)
% 0.38/0.58          | ~ (r2_hidden @ X6 @ X7)
% 0.38/0.58          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.38/0.58  thf('65', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r2_hidden @ k1_xboole_0 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['63', '64'])).
% 0.38/0.58  thf('66', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.38/0.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.38/0.58  thf('67', plain,
% 0.38/0.58      (![X4 : $i, X5 : $i]:
% 0.38/0.58         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.38/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.38/0.58  thf('68', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.38/0.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.38/0.58  thf('69', plain,
% 0.38/0.58      (![X1 : $i, X3 : $i]:
% 0.38/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.58  thf('70', plain,
% 0.38/0.58      (![X1 : $i, X3 : $i]:
% 0.38/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.58  thf('71', plain,
% 0.38/0.58      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X6 @ X4)
% 0.38/0.58          | ~ (r2_hidden @ X6 @ X7)
% 0.38/0.58          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.38/0.58  thf('72', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         ((r1_tarski @ X0 @ X1)
% 0.38/0.58          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.38/0.58          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.38/0.58      inference('sup-', [status(thm)], ['70', '71'])).
% 0.38/0.58  thf('73', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((r1_tarski @ X0 @ X1)
% 0.38/0.58          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.38/0.58          | (r1_tarski @ X0 @ X1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['69', '72'])).
% 0.38/0.58  thf('74', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (r1_tarski @ X0 @ X1))),
% 0.38/0.58      inference('simplify', [status(thm)], ['73'])).
% 0.38/0.58  thf('75', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.58      inference('sup-', [status(thm)], ['68', '74'])).
% 0.38/0.58  thf('76', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.38/0.58          | (r2_hidden @ X0 @ X2)
% 0.38/0.58          | ~ (r1_tarski @ X1 @ X2))),
% 0.38/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.58  thf('77', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['75', '76'])).
% 0.38/0.58  thf('78', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.38/0.58          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['67', '77'])).
% 0.38/0.58  thf('79', plain,
% 0.38/0.58      (![X4 : $i, X5 : $i]:
% 0.38/0.58         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.38/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.38/0.58  thf('80', plain,
% 0.38/0.58      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X6 @ X4)
% 0.38/0.58          | ~ (r2_hidden @ X6 @ X7)
% 0.38/0.58          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.38/0.58  thf('81', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         ((r1_xboole_0 @ X0 @ X1)
% 0.38/0.58          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.38/0.58          | ~ (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2))),
% 0.38/0.58      inference('sup-', [status(thm)], ['79', '80'])).
% 0.38/0.58  thf('82', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((r1_xboole_0 @ k1_xboole_0 @ X1)
% 0.38/0.58          | ~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.38/0.58          | (r1_xboole_0 @ k1_xboole_0 @ X1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['78', '81'])).
% 0.38/0.58  thf('83', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (r1_xboole_0 @ k1_xboole_0 @ X0) | (r1_xboole_0 @ k1_xboole_0 @ X1))),
% 0.38/0.58      inference('simplify', [status(thm)], ['82'])).
% 0.38/0.58  thf('84', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.38/0.58      inference('sup-', [status(thm)], ['66', '83'])).
% 0.38/0.58  thf('85', plain, (![X0 : $i]: ~ (r2_hidden @ k1_xboole_0 @ X0)),
% 0.38/0.58      inference('demod', [status(thm)], ['65', '84'])).
% 0.38/0.58  thf('86', plain, ($false), inference('sup-', [status(thm)], ['62', '85'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DDKOQHSLnD

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:42 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 176 expanded)
%              Number of leaves         :   24 (  57 expanded)
%              Depth                    :   19
%              Number of atoms          :  995 (2054 expanded)
%              Number of equality atoms :   59 ( 113 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_xboole_0 @ X11 @ X13 )
      | ( ( k4_xboole_0 @ X11 @ X13 )
       != X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['5'])).

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

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X25 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('22',plain,(
    ! [X28: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X28 ) @ ( sk_C_1 @ X28 ) ) @ X28 )
      | ( X28 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf(d8_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( C
                  = ( k5_relat_1 @ A @ B ) )
              <=> ! [D: $i,E: $i] :
                    ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                  <=> ? [F: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B )
                        & ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( X18
       != ( k5_relat_1 @ X17 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X22 @ X19 @ X16 @ X17 ) @ X22 ) @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X22 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('24',plain,(
    ! [X16: $i,X17: $i,X19: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X22 ) @ ( k5_relat_1 @ X17 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X22 @ X19 @ X16 @ X17 ) @ X22 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('30',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','33'])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('35',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('36',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('44',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X25 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('45',plain,(
    ! [X28: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X28 ) @ ( sk_C_1 @ X28 ) ) @ X28 )
      | ( X28 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('46',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( X18
       != ( k5_relat_1 @ X17 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_F_1 @ X22 @ X19 @ X16 @ X17 ) ) @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X22 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('47',plain,(
    ! [X16: $i,X17: $i,X19: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X22 ) @ ( k5_relat_1 @ X17 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_F_1 @ X22 @ X19 @ X16 @ X17 ) ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_C_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_C_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_C_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_C_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_C_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('53',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( sk_F_1 @ ( sk_C_1 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( sk_B @ ( k5_relat_1 @ X0 @ X1 ) ) @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','56'])).

thf('58',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','38'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('61',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('66',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['64','65'])).

thf('67',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['42','66'])).

thf('68',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference(simplify,[status(thm)],['70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DDKOQHSLnD
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 292 iterations in 0.121s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.58  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 0.37/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.37/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.58  thf(d10_xboole_0, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.58  thf('0', plain,
% 0.37/0.58      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.37/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.58  thf('1', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.37/0.58      inference('simplify', [status(thm)], ['0'])).
% 0.37/0.58  thf(l32_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.58  thf('2', plain,
% 0.37/0.58      (![X7 : $i, X9 : $i]:
% 0.37/0.58         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.37/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.58  thf('3', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.58  thf(t83_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.58  thf('4', plain,
% 0.37/0.58      (![X11 : $i, X13 : $i]:
% 0.37/0.58         ((r1_xboole_0 @ X11 @ X13) | ((k4_xboole_0 @ X11 @ X13) != (X11)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.37/0.58  thf('5', plain,
% 0.37/0.58      (![X0 : $i]: (((k1_xboole_0) != (X0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.58  thf('6', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.37/0.58      inference('simplify', [status(thm)], ['5'])).
% 0.37/0.58  thf(t3_xboole_0, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.37/0.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.37/0.58            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.37/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.58  thf('8', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.37/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.58  thf('9', plain,
% 0.37/0.58      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X2 @ X0)
% 0.37/0.58          | ~ (r2_hidden @ X2 @ X3)
% 0.37/0.58          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.37/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.58  thf('10', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         ((r1_xboole_0 @ X0 @ X1)
% 0.37/0.58          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.37/0.58          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.37/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.58  thf('11', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((r1_xboole_0 @ X0 @ X1)
% 0.37/0.58          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.37/0.58          | (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['7', '10'])).
% 0.37/0.58  thf('12', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.58      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.58  thf('13', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.37/0.58      inference('sup-', [status(thm)], ['6', '12'])).
% 0.37/0.58  thf('14', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.37/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.58  thf('15', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.37/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.58  thf('16', plain,
% 0.37/0.58      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X2 @ X0)
% 0.37/0.58          | ~ (r2_hidden @ X2 @ X3)
% 0.37/0.58          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.37/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.58  thf('17', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         ((r1_xboole_0 @ X1 @ X0)
% 0.37/0.58          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.37/0.58          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.37/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.58  thf('18', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((r1_xboole_0 @ X0 @ X1)
% 0.37/0.58          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.37/0.58          | (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['14', '17'])).
% 0.37/0.58  thf('19', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.58      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.58  thf('20', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.37/0.58      inference('sup-', [status(thm)], ['13', '19'])).
% 0.37/0.58  thf(dt_k5_relat_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.37/0.58       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.37/0.58  thf('21', plain,
% 0.37/0.58      (![X24 : $i, X25 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X24)
% 0.37/0.58          | ~ (v1_relat_1 @ X25)
% 0.37/0.58          | (v1_relat_1 @ (k5_relat_1 @ X24 @ X25)))),
% 0.37/0.58      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.37/0.58  thf(t56_relat_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( v1_relat_1 @ A ) =>
% 0.37/0.58       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.37/0.58         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.58  thf('22', plain,
% 0.37/0.58      (![X28 : $i]:
% 0.37/0.58         ((r2_hidden @ (k4_tarski @ (sk_B @ X28) @ (sk_C_1 @ X28)) @ X28)
% 0.37/0.58          | ((X28) = (k1_xboole_0))
% 0.37/0.58          | ~ (v1_relat_1 @ X28))),
% 0.37/0.58      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.37/0.58  thf(d8_relat_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( v1_relat_1 @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( v1_relat_1 @ B ) =>
% 0.37/0.58           ( ![C:$i]:
% 0.37/0.58             ( ( v1_relat_1 @ C ) =>
% 0.37/0.58               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 0.37/0.58                 ( ![D:$i,E:$i]:
% 0.37/0.58                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.37/0.58                     ( ?[F:$i]:
% 0.37/0.58                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 0.37/0.58                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.58  thf('23', plain,
% 0.37/0.58      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X22 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X16)
% 0.37/0.58          | ((X18) != (k5_relat_1 @ X17 @ X16))
% 0.37/0.58          | (r2_hidden @ 
% 0.37/0.58             (k4_tarski @ (sk_F_1 @ X22 @ X19 @ X16 @ X17) @ X22) @ X16)
% 0.37/0.58          | ~ (r2_hidden @ (k4_tarski @ X19 @ X22) @ X18)
% 0.37/0.58          | ~ (v1_relat_1 @ X18)
% 0.37/0.58          | ~ (v1_relat_1 @ X17))),
% 0.37/0.58      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.37/0.58  thf('24', plain,
% 0.37/0.58      (![X16 : $i, X17 : $i, X19 : $i, X22 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X17)
% 0.37/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X17 @ X16))
% 0.37/0.58          | ~ (r2_hidden @ (k4_tarski @ X19 @ X22) @ (k5_relat_1 @ X17 @ X16))
% 0.37/0.58          | (r2_hidden @ 
% 0.37/0.58             (k4_tarski @ (sk_F_1 @ X22 @ X19 @ X16 @ X17) @ X22) @ X16)
% 0.37/0.58          | ~ (v1_relat_1 @ X16))),
% 0.37/0.58      inference('simplify', [status(thm)], ['23'])).
% 0.37/0.58  thf('25', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.37/0.58          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | (r2_hidden @ 
% 0.37/0.58             (k4_tarski @ 
% 0.37/0.58              (sk_F_1 @ (sk_C_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.37/0.58               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.37/0.58              (sk_C_1 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.37/0.58             X0)
% 0.37/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.37/0.58          | ~ (v1_relat_1 @ X1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['22', '24'])).
% 0.37/0.58  thf('26', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X1)
% 0.37/0.58          | (r2_hidden @ 
% 0.37/0.58             (k4_tarski @ 
% 0.37/0.58              (sk_F_1 @ (sk_C_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.37/0.58               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.37/0.58              (sk_C_1 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.37/0.58             X0)
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.37/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['25'])).
% 0.37/0.58  thf('27', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X0)
% 0.37/0.58          | ~ (v1_relat_1 @ X1)
% 0.37/0.58          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | (r2_hidden @ 
% 0.37/0.58             (k4_tarski @ 
% 0.37/0.58              (sk_F_1 @ (sk_C_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.37/0.58               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.37/0.58              (sk_C_1 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.37/0.58             X0)
% 0.37/0.58          | ~ (v1_relat_1 @ X1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['21', '26'])).
% 0.37/0.58  thf('28', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((r2_hidden @ 
% 0.37/0.58           (k4_tarski @ 
% 0.37/0.58            (sk_F_1 @ (sk_C_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.37/0.58             (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.37/0.58            (sk_C_1 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.37/0.58           X0)
% 0.37/0.58          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.37/0.58          | ~ (v1_relat_1 @ X1)
% 0.37/0.58          | ~ (v1_relat_1 @ X0))),
% 0.37/0.58      inference('simplify', [status(thm)], ['27'])).
% 0.37/0.58  thf('29', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((r2_hidden @ 
% 0.37/0.58           (k4_tarski @ 
% 0.37/0.58            (sk_F_1 @ (sk_C_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.37/0.58             (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.37/0.58            (sk_C_1 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.37/0.58           X0)
% 0.37/0.58          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.37/0.58          | ~ (v1_relat_1 @ X1)
% 0.37/0.58          | ~ (v1_relat_1 @ X0))),
% 0.37/0.58      inference('simplify', [status(thm)], ['27'])).
% 0.37/0.58  thf('30', plain,
% 0.37/0.58      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X2 @ X0)
% 0.37/0.58          | ~ (r2_hidden @ X2 @ X3)
% 0.37/0.58          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.37/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.58  thf('31', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X0)
% 0.37/0.58          | ~ (v1_relat_1 @ X1)
% 0.37/0.58          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.37/0.58          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.37/0.58          | ~ (r2_hidden @ 
% 0.37/0.58               (k4_tarski @ 
% 0.37/0.58                (sk_F_1 @ (sk_C_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.37/0.58                 (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.37/0.58                (sk_C_1 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.37/0.58               X2))),
% 0.37/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.58  thf('32', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X0)
% 0.37/0.58          | ~ (v1_relat_1 @ X1)
% 0.37/0.58          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.37/0.58          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.37/0.58          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.37/0.58          | ~ (v1_relat_1 @ X1)
% 0.37/0.58          | ~ (v1_relat_1 @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['28', '31'])).
% 0.37/0.58  thf('33', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (r1_xboole_0 @ X0 @ X0)
% 0.37/0.58          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.37/0.58          | ~ (v1_relat_1 @ X1)
% 0.37/0.58          | ~ (v1_relat_1 @ X0))),
% 0.37/0.58      inference('simplify', [status(thm)], ['32'])).
% 0.37/0.58  thf('34', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['20', '33'])).
% 0.37/0.58  thf(t62_relat_1, conjecture,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( v1_relat_1 @ A ) =>
% 0.37/0.58       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.37/0.58         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i]:
% 0.37/0.58        ( ( v1_relat_1 @ A ) =>
% 0.37/0.58          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.37/0.58            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.37/0.58  thf('35', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t2_boole, axiom,
% 0.37/0.58    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.58  thf('36', plain,
% 0.37/0.58      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.37/0.58  thf(fc1_relat_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.58  thf('37', plain,
% 0.37/0.58      (![X26 : $i, X27 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X26) | (v1_relat_1 @ (k3_xboole_0 @ X26 @ X27)))),
% 0.37/0.58      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.37/0.58  thf('38', plain,
% 0.37/0.58      (![X0 : $i]: ((v1_relat_1 @ k1_xboole_0) | ~ (v1_relat_1 @ X0))),
% 0.37/0.58      inference('sup+', [status(thm)], ['36', '37'])).
% 0.37/0.58  thf('39', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.58      inference('sup-', [status(thm)], ['35', '38'])).
% 0.37/0.58  thf('40', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X0)
% 0.37/0.58          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.37/0.58      inference('demod', [status(thm)], ['34', '39'])).
% 0.37/0.58  thf('41', plain,
% 0.37/0.58      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.37/0.58        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('42', plain,
% 0.37/0.58      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.37/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.58      inference('split', [status(esa)], ['41'])).
% 0.37/0.58  thf('43', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.37/0.58      inference('sup-', [status(thm)], ['13', '19'])).
% 0.37/0.58  thf('44', plain,
% 0.37/0.58      (![X24 : $i, X25 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X24)
% 0.37/0.58          | ~ (v1_relat_1 @ X25)
% 0.37/0.58          | (v1_relat_1 @ (k5_relat_1 @ X24 @ X25)))),
% 0.37/0.58      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.37/0.58  thf('45', plain,
% 0.37/0.58      (![X28 : $i]:
% 0.37/0.58         ((r2_hidden @ (k4_tarski @ (sk_B @ X28) @ (sk_C_1 @ X28)) @ X28)
% 0.37/0.58          | ((X28) = (k1_xboole_0))
% 0.37/0.58          | ~ (v1_relat_1 @ X28))),
% 0.37/0.58      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.37/0.58  thf('46', plain,
% 0.37/0.58      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X22 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X16)
% 0.37/0.58          | ((X18) != (k5_relat_1 @ X17 @ X16))
% 0.37/0.58          | (r2_hidden @ 
% 0.37/0.58             (k4_tarski @ X19 @ (sk_F_1 @ X22 @ X19 @ X16 @ X17)) @ X17)
% 0.37/0.58          | ~ (r2_hidden @ (k4_tarski @ X19 @ X22) @ X18)
% 0.37/0.58          | ~ (v1_relat_1 @ X18)
% 0.37/0.58          | ~ (v1_relat_1 @ X17))),
% 0.37/0.58      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.37/0.58  thf('47', plain,
% 0.37/0.58      (![X16 : $i, X17 : $i, X19 : $i, X22 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X17)
% 0.37/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X17 @ X16))
% 0.37/0.58          | ~ (r2_hidden @ (k4_tarski @ X19 @ X22) @ (k5_relat_1 @ X17 @ X16))
% 0.37/0.58          | (r2_hidden @ 
% 0.37/0.58             (k4_tarski @ X19 @ (sk_F_1 @ X22 @ X19 @ X16 @ X17)) @ X17)
% 0.37/0.58          | ~ (v1_relat_1 @ X16))),
% 0.37/0.58      inference('simplify', [status(thm)], ['46'])).
% 0.37/0.58  thf('48', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.37/0.58          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | (r2_hidden @ 
% 0.37/0.58             (k4_tarski @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.37/0.58              (sk_F_1 @ (sk_C_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.37/0.58               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 0.37/0.58             X1)
% 0.37/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.37/0.58          | ~ (v1_relat_1 @ X1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['45', '47'])).
% 0.37/0.58  thf('49', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X1)
% 0.37/0.58          | (r2_hidden @ 
% 0.37/0.58             (k4_tarski @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.37/0.58              (sk_F_1 @ (sk_C_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.37/0.58               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 0.37/0.58             X1)
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.37/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['48'])).
% 0.37/0.58  thf('50', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X0)
% 0.37/0.58          | ~ (v1_relat_1 @ X1)
% 0.37/0.58          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | (r2_hidden @ 
% 0.37/0.58             (k4_tarski @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.37/0.58              (sk_F_1 @ (sk_C_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.37/0.58               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 0.37/0.58             X1)
% 0.37/0.58          | ~ (v1_relat_1 @ X1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['44', '49'])).
% 0.37/0.58  thf('51', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((r2_hidden @ 
% 0.37/0.58           (k4_tarski @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.37/0.58            (sk_F_1 @ (sk_C_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.37/0.58             (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 0.37/0.58           X1)
% 0.37/0.58          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.37/0.58          | ~ (v1_relat_1 @ X1)
% 0.37/0.58          | ~ (v1_relat_1 @ X0))),
% 0.37/0.58      inference('simplify', [status(thm)], ['50'])).
% 0.37/0.58  thf('52', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((r2_hidden @ 
% 0.37/0.58           (k4_tarski @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.37/0.58            (sk_F_1 @ (sk_C_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.37/0.58             (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 0.37/0.58           X1)
% 0.37/0.58          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.37/0.58          | ~ (v1_relat_1 @ X1)
% 0.37/0.58          | ~ (v1_relat_1 @ X0))),
% 0.37/0.58      inference('simplify', [status(thm)], ['50'])).
% 0.37/0.58  thf('53', plain,
% 0.37/0.58      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X2 @ X0)
% 0.37/0.58          | ~ (r2_hidden @ X2 @ X3)
% 0.37/0.58          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.37/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.58  thf('54', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X1)
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | ((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.37/0.58          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.37/0.58          | ~ (r2_hidden @ 
% 0.37/0.58               (k4_tarski @ (sk_B @ (k5_relat_1 @ X0 @ X1)) @ 
% 0.37/0.58                (sk_F_1 @ (sk_C_1 @ (k5_relat_1 @ X0 @ X1)) @ 
% 0.37/0.58                 (sk_B @ (k5_relat_1 @ X0 @ X1)) @ X1 @ X0)) @ 
% 0.37/0.58               X2))),
% 0.37/0.58      inference('sup-', [status(thm)], ['52', '53'])).
% 0.37/0.58  thf('55', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X1)
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | ((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.37/0.58          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.37/0.58          | ((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | ~ (v1_relat_1 @ X1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['51', '54'])).
% 0.37/0.58  thf('56', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (~ (r1_xboole_0 @ X0 @ X0)
% 0.37/0.58          | ((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | ~ (v1_relat_1 @ X1))),
% 0.37/0.58      inference('simplify', [status(thm)], ['55'])).
% 0.37/0.58  thf('57', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X0)
% 0.37/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.58          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['43', '56'])).
% 0.37/0.58  thf('58', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.58      inference('sup-', [status(thm)], ['35', '38'])).
% 0.37/0.58  thf('59', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X0)
% 0.37/0.58          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.37/0.58      inference('demod', [status(thm)], ['57', '58'])).
% 0.37/0.58  thf('60', plain,
% 0.37/0.58      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.37/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.58      inference('split', [status(esa)], ['41'])).
% 0.37/0.58  thf('61', plain,
% 0.37/0.58      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.37/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['59', '60'])).
% 0.37/0.58  thf('62', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('63', plain,
% 0.37/0.58      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.37/0.58         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.58      inference('demod', [status(thm)], ['61', '62'])).
% 0.37/0.58  thf('64', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['63'])).
% 0.37/0.58  thf('65', plain,
% 0.37/0.58      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.37/0.58       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.37/0.58      inference('split', [status(esa)], ['41'])).
% 0.37/0.58  thf('66', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.37/0.58      inference('sat_resolution*', [status(thm)], ['64', '65'])).
% 0.37/0.58  thf('67', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.58      inference('simpl_trail', [status(thm)], ['42', '66'])).
% 0.37/0.58  thf('68', plain,
% 0.37/0.58      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['40', '67'])).
% 0.37/0.58  thf('69', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('70', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.58      inference('demod', [status(thm)], ['68', '69'])).
% 0.37/0.58  thf('71', plain, ($false), inference('simplify', [status(thm)], ['70'])).
% 0.37/0.58  
% 0.37/0.58  % SZS output end Refutation
% 0.37/0.58  
% 0.37/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

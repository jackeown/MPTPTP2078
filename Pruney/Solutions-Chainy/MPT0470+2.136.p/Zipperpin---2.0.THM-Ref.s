%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jUEdNCtkBI

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:46 EST 2020

% Result     : Theorem 0.33s
% Output     : Refutation 0.33s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 237 expanded)
%              Number of leaves         :   26 (  81 expanded)
%              Depth                    :   22
%              Number of atoms          : 1088 (2557 expanded)
%              Number of equality atoms :   56 ( 151 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X22 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X25: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X25 ) @ ( sk_C_2 @ X25 ) ) @ X25 )
      | ( X25 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
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

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( X15
       != ( k5_relat_1 @ X14 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X19 @ X16 @ X13 @ X14 ) @ X19 ) @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X19 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('4',plain,(
    ! [X13: $i,X14: $i,X16: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X19 ) @ ( k5_relat_1 @ X14 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X19 @ X16 @ X13 @ X14 ) @ X19 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

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

thf('10',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
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
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','13'])).

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

thf('15',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X15 @ X13 @ X14 ) @ ( sk_E @ X15 @ X13 @ X14 ) ) @ X15 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X15 @ X13 @ X14 ) @ ( sk_F @ X15 @ X13 @ X14 ) ) @ X14 )
      | ( X15
        = ( k5_relat_1 @ X14 @ X13 ) )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X15 @ X13 @ X14 ) @ ( sk_E @ X15 @ X13 @ X14 ) ) @ X15 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X15 @ X13 @ X14 ) @ ( sk_F @ X15 @ X13 @ X14 ) ) @ X14 )
      | ( X15
        = ( k5_relat_1 @ X14 @ X13 ) )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('25',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','18'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ ( sk_E @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ ( sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','18'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ ( sk_E @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ ( sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X1 @ k1_xboole_0 ) @ ( sk_F @ k1_xboole_0 @ X1 @ k1_xboole_0 ) ) @ X3 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X1 @ k1_xboole_0 ) @ ( sk_E @ k1_xboole_0 @ X1 @ k1_xboole_0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ ( sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_xboole_0 @ X1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ ( sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','36'])).

thf('38',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','18'])).

thf('39',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','18'])).

thf('40',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ ( sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ ( sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ ( sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ ( sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ ( sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['42'])).

thf('44',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ ( sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('47',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('51',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ ( sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['45','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ ( sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['42'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ ( sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['56','59'])).

thf('61',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('62',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('67',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['65','66'])).

thf('68',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['22','67'])).

thf('69',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference(simplify,[status(thm)],['71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jUEdNCtkBI
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:03:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.33/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.33/0.52  % Solved by: fo/fo7.sh
% 0.33/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.33/0.52  % done 95 iterations in 0.075s
% 0.33/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.33/0.52  % SZS output start Refutation
% 0.33/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.33/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.33/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.33/0.52  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.33/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.33/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.33/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.33/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.33/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.33/0.52  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 0.33/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.33/0.52  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.33/0.52  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.33/0.52  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.33/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.33/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.33/0.52  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.33/0.52  thf('0', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 0.33/0.52      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.33/0.52  thf(dt_k5_relat_1, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.33/0.52       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.33/0.52  thf('1', plain,
% 0.33/0.52      (![X21 : $i, X22 : $i]:
% 0.33/0.52         (~ (v1_relat_1 @ X21)
% 0.33/0.52          | ~ (v1_relat_1 @ X22)
% 0.33/0.52          | (v1_relat_1 @ (k5_relat_1 @ X21 @ X22)))),
% 0.33/0.52      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.33/0.52  thf(t56_relat_1, axiom,
% 0.33/0.52    (![A:$i]:
% 0.33/0.52     ( ( v1_relat_1 @ A ) =>
% 0.33/0.52       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.33/0.52         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.33/0.52  thf('2', plain,
% 0.33/0.52      (![X25 : $i]:
% 0.33/0.52         ((r2_hidden @ (k4_tarski @ (sk_B @ X25) @ (sk_C_2 @ X25)) @ X25)
% 0.33/0.52          | ((X25) = (k1_xboole_0))
% 0.33/0.52          | ~ (v1_relat_1 @ X25))),
% 0.33/0.52      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.33/0.52  thf(d8_relat_1, axiom,
% 0.33/0.52    (![A:$i]:
% 0.33/0.52     ( ( v1_relat_1 @ A ) =>
% 0.33/0.52       ( ![B:$i]:
% 0.33/0.52         ( ( v1_relat_1 @ B ) =>
% 0.33/0.52           ( ![C:$i]:
% 0.33/0.52             ( ( v1_relat_1 @ C ) =>
% 0.33/0.52               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 0.33/0.52                 ( ![D:$i,E:$i]:
% 0.33/0.52                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.33/0.52                     ( ?[F:$i]:
% 0.33/0.52                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 0.33/0.52                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.33/0.52  thf('3', plain,
% 0.33/0.52      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X19 : $i]:
% 0.33/0.52         (~ (v1_relat_1 @ X13)
% 0.33/0.52          | ((X15) != (k5_relat_1 @ X14 @ X13))
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_F_1 @ X19 @ X16 @ X13 @ X14) @ X19) @ X13)
% 0.33/0.52          | ~ (r2_hidden @ (k4_tarski @ X16 @ X19) @ X15)
% 0.33/0.52          | ~ (v1_relat_1 @ X15)
% 0.33/0.52          | ~ (v1_relat_1 @ X14))),
% 0.33/0.52      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.33/0.52  thf('4', plain,
% 0.33/0.52      (![X13 : $i, X14 : $i, X16 : $i, X19 : $i]:
% 0.33/0.52         (~ (v1_relat_1 @ X14)
% 0.33/0.52          | ~ (v1_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 0.33/0.52          | ~ (r2_hidden @ (k4_tarski @ X16 @ X19) @ (k5_relat_1 @ X14 @ X13))
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_F_1 @ X19 @ X16 @ X13 @ X14) @ X19) @ X13)
% 0.33/0.52          | ~ (v1_relat_1 @ X13))),
% 0.33/0.52      inference('simplify', [status(thm)], ['3'])).
% 0.33/0.52  thf('5', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.33/0.52          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.33/0.52          | ~ (v1_relat_1 @ X0)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ 
% 0.33/0.52              (sk_F_1 @ (sk_C_2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.33/0.52               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.33/0.52              (sk_C_2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.33/0.52             X0)
% 0.33/0.52          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.33/0.52          | ~ (v1_relat_1 @ X1))),
% 0.33/0.52      inference('sup-', [status(thm)], ['2', '4'])).
% 0.33/0.52  thf('6', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         (~ (v1_relat_1 @ X1)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ 
% 0.33/0.52              (sk_F_1 @ (sk_C_2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.33/0.52               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.33/0.52              (sk_C_2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.33/0.52             X0)
% 0.33/0.52          | ~ (v1_relat_1 @ X0)
% 0.33/0.52          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.33/0.52          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.33/0.52      inference('simplify', [status(thm)], ['5'])).
% 0.33/0.52  thf('7', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         (~ (v1_relat_1 @ X0)
% 0.33/0.52          | ~ (v1_relat_1 @ X1)
% 0.33/0.52          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.33/0.52          | ~ (v1_relat_1 @ X0)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ 
% 0.33/0.52              (sk_F_1 @ (sk_C_2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.33/0.52               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.33/0.52              (sk_C_2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.33/0.52             X0)
% 0.33/0.52          | ~ (v1_relat_1 @ X1))),
% 0.33/0.52      inference('sup-', [status(thm)], ['1', '6'])).
% 0.33/0.52  thf('8', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         ((r2_hidden @ 
% 0.33/0.52           (k4_tarski @ 
% 0.33/0.52            (sk_F_1 @ (sk_C_2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.33/0.52             (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.33/0.52            (sk_C_2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.33/0.52           X0)
% 0.33/0.52          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.33/0.52          | ~ (v1_relat_1 @ X1)
% 0.33/0.52          | ~ (v1_relat_1 @ X0))),
% 0.33/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.33/0.52  thf('9', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         ((r2_hidden @ 
% 0.33/0.52           (k4_tarski @ 
% 0.33/0.52            (sk_F_1 @ (sk_C_2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.33/0.52             (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.33/0.52            (sk_C_2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.33/0.52           X0)
% 0.33/0.52          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.33/0.52          | ~ (v1_relat_1 @ X1)
% 0.33/0.52          | ~ (v1_relat_1 @ X0))),
% 0.33/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.33/0.52  thf(t3_xboole_0, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.33/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.33/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.33/0.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.33/0.52  thf('10', plain,
% 0.33/0.52      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X6 @ X4)
% 0.33/0.52          | ~ (r2_hidden @ X6 @ X7)
% 0.33/0.52          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.33/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.33/0.52  thf('11', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.33/0.52         (~ (v1_relat_1 @ X0)
% 0.33/0.52          | ~ (v1_relat_1 @ X1)
% 0.33/0.52          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.33/0.52          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.33/0.52          | ~ (r2_hidden @ 
% 0.33/0.52               (k4_tarski @ 
% 0.33/0.52                (sk_F_1 @ (sk_C_2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.33/0.52                 (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.33/0.52                (sk_C_2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.33/0.52               X2))),
% 0.33/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.33/0.52  thf('12', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         (~ (v1_relat_1 @ X0)
% 0.33/0.52          | ~ (v1_relat_1 @ X1)
% 0.33/0.52          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.33/0.52          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.33/0.52          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.33/0.52          | ~ (v1_relat_1 @ X1)
% 0.33/0.52          | ~ (v1_relat_1 @ X0))),
% 0.33/0.52      inference('sup-', [status(thm)], ['8', '11'])).
% 0.33/0.52  thf('13', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         (~ (r1_xboole_0 @ X0 @ X0)
% 0.33/0.52          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.33/0.52          | ~ (v1_relat_1 @ X1)
% 0.33/0.52          | ~ (v1_relat_1 @ X0))),
% 0.33/0.52      inference('simplify', [status(thm)], ['12'])).
% 0.33/0.52  thf('14', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         (~ (v1_relat_1 @ k1_xboole_0)
% 0.33/0.52          | ~ (v1_relat_1 @ X0)
% 0.33/0.52          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.33/0.52      inference('sup-', [status(thm)], ['0', '13'])).
% 0.33/0.52  thf(t62_relat_1, conjecture,
% 0.33/0.52    (![A:$i]:
% 0.33/0.52     ( ( v1_relat_1 @ A ) =>
% 0.33/0.52       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.33/0.52         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.33/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.33/0.52    (~( ![A:$i]:
% 0.33/0.52        ( ( v1_relat_1 @ A ) =>
% 0.33/0.52          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.33/0.52            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.33/0.52    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.33/0.52  thf('15', plain, ((v1_relat_1 @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf(t2_boole, axiom,
% 0.33/0.52    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.33/0.52  thf('16', plain,
% 0.33/0.52      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.33/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.33/0.52  thf(fc1_relat_1, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.33/0.52  thf('17', plain,
% 0.33/0.52      (![X23 : $i, X24 : $i]:
% 0.33/0.52         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k3_xboole_0 @ X23 @ X24)))),
% 0.33/0.52      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.33/0.52  thf('18', plain,
% 0.33/0.52      (![X0 : $i]: ((v1_relat_1 @ k1_xboole_0) | ~ (v1_relat_1 @ X0))),
% 0.33/0.52      inference('sup+', [status(thm)], ['16', '17'])).
% 0.33/0.52  thf('19', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.33/0.52      inference('sup-', [status(thm)], ['15', '18'])).
% 0.33/0.52  thf('20', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         (~ (v1_relat_1 @ X0)
% 0.33/0.52          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.33/0.52      inference('demod', [status(thm)], ['14', '19'])).
% 0.33/0.52  thf('21', plain,
% 0.33/0.52      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.33/0.52        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('22', plain,
% 0.33/0.52      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.33/0.52         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.33/0.52      inference('split', [status(esa)], ['21'])).
% 0.33/0.52  thf('23', plain,
% 0.33/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.33/0.52         (~ (v1_relat_1 @ X13)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_D @ X15 @ X13 @ X14) @ (sk_E @ X15 @ X13 @ X14)) @ 
% 0.33/0.52             X15)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_D @ X15 @ X13 @ X14) @ (sk_F @ X15 @ X13 @ X14)) @ 
% 0.33/0.52             X14)
% 0.33/0.52          | ((X15) = (k5_relat_1 @ X14 @ X13))
% 0.33/0.52          | ~ (v1_relat_1 @ X15)
% 0.33/0.52          | ~ (v1_relat_1 @ X14))),
% 0.33/0.52      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.33/0.52  thf('24', plain,
% 0.33/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.33/0.52         (~ (v1_relat_1 @ X13)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_D @ X15 @ X13 @ X14) @ (sk_E @ X15 @ X13 @ X14)) @ 
% 0.33/0.52             X15)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_D @ X15 @ X13 @ X14) @ (sk_F @ X15 @ X13 @ X14)) @ 
% 0.33/0.52             X14)
% 0.33/0.52          | ((X15) = (k5_relat_1 @ X14 @ X13))
% 0.33/0.52          | ~ (v1_relat_1 @ X15)
% 0.33/0.52          | ~ (v1_relat_1 @ X14))),
% 0.33/0.52      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.33/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.33/0.52  thf('25', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.33/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.33/0.52  thf(d3_tarski, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.33/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.33/0.52  thf('26', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.33/0.52          | (r2_hidden @ X0 @ X2)
% 0.33/0.52          | ~ (r1_tarski @ X1 @ X2))),
% 0.33/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.33/0.52  thf('27', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.33/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.33/0.52  thf('28', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.33/0.52         (~ (v1_relat_1 @ X0)
% 0.33/0.52          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.33/0.52          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ 
% 0.33/0.52              (sk_F @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.33/0.52             X0)
% 0.33/0.52          | ~ (v1_relat_1 @ X1)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ 
% 0.33/0.52              (sk_E @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.33/0.52             X2))),
% 0.33/0.52      inference('sup-', [status(thm)], ['24', '27'])).
% 0.33/0.52  thf('29', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.33/0.52      inference('sup-', [status(thm)], ['15', '18'])).
% 0.33/0.52  thf('30', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.33/0.52         (~ (v1_relat_1 @ X0)
% 0.33/0.52          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ 
% 0.33/0.52              (sk_F @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.33/0.52             X0)
% 0.33/0.52          | ~ (v1_relat_1 @ X1)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ 
% 0.33/0.52              (sk_E @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.33/0.52             X2))),
% 0.33/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.33/0.52  thf('31', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.33/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.33/0.52  thf('32', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.33/0.52         ((r2_hidden @ 
% 0.33/0.52           (k4_tarski @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.33/0.52            (sk_E @ k1_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.33/0.52           X2)
% 0.33/0.52          | ~ (v1_relat_1 @ X0)
% 0.33/0.52          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.33/0.52          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.33/0.52              (sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.33/0.52             X1))),
% 0.33/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.33/0.52  thf('33', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.33/0.52      inference('sup-', [status(thm)], ['15', '18'])).
% 0.33/0.52  thf('34', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.33/0.52         ((r2_hidden @ 
% 0.33/0.52           (k4_tarski @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.33/0.52            (sk_E @ k1_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.33/0.52           X2)
% 0.33/0.52          | ~ (v1_relat_1 @ X0)
% 0.33/0.52          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.33/0.52              (sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.33/0.52             X1))),
% 0.33/0.52      inference('demod', [status(thm)], ['32', '33'])).
% 0.33/0.52  thf('35', plain,
% 0.33/0.52      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X6 @ X4)
% 0.33/0.52          | ~ (r2_hidden @ X6 @ X7)
% 0.33/0.52          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.33/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.33/0.52  thf('36', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.33/0.52         ((r2_hidden @ 
% 0.33/0.52           (k4_tarski @ (sk_D @ k1_xboole_0 @ X1 @ k1_xboole_0) @ 
% 0.33/0.52            (sk_F @ k1_xboole_0 @ X1 @ k1_xboole_0)) @ 
% 0.33/0.52           X3)
% 0.33/0.52          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X1))
% 0.33/0.52          | ~ (v1_relat_1 @ X1)
% 0.33/0.52          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.33/0.52          | ~ (r2_hidden @ 
% 0.33/0.52               (k4_tarski @ (sk_D @ k1_xboole_0 @ X1 @ k1_xboole_0) @ 
% 0.33/0.52                (sk_E @ k1_xboole_0 @ X1 @ k1_xboole_0)) @ 
% 0.33/0.52               X2))),
% 0.33/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.33/0.52  thf('37', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.33/0.52         (~ (v1_relat_1 @ k1_xboole_0)
% 0.33/0.52          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.33/0.52          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.33/0.52              (sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.33/0.52             k1_xboole_0)
% 0.33/0.52          | ~ (v1_relat_1 @ X0)
% 0.33/0.52          | ~ (r1_xboole_0 @ X1 @ k1_xboole_0)
% 0.33/0.52          | ~ (v1_relat_1 @ X0)
% 0.33/0.52          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.33/0.52              (sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.33/0.52             X2))),
% 0.33/0.52      inference('sup-', [status(thm)], ['23', '36'])).
% 0.33/0.52  thf('38', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.33/0.52      inference('sup-', [status(thm)], ['15', '18'])).
% 0.33/0.52  thf('39', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.33/0.52      inference('sup-', [status(thm)], ['15', '18'])).
% 0.33/0.52  thf('40', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 0.33/0.52      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.33/0.52  thf('41', plain,
% 0.33/0.52      (![X0 : $i, X2 : $i]:
% 0.33/0.52         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.33/0.52              (sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.33/0.52             k1_xboole_0)
% 0.33/0.52          | ~ (v1_relat_1 @ X0)
% 0.33/0.52          | ~ (v1_relat_1 @ X0)
% 0.33/0.52          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.33/0.52              (sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.33/0.52             X2))),
% 0.33/0.52      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.33/0.52  thf('42', plain,
% 0.33/0.52      (![X0 : $i, X2 : $i]:
% 0.33/0.52         ((r2_hidden @ 
% 0.33/0.52           (k4_tarski @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.33/0.52            (sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.33/0.52           X2)
% 0.33/0.52          | ~ (v1_relat_1 @ X0)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.33/0.52              (sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.33/0.52             k1_xboole_0)
% 0.33/0.52          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.33/0.52      inference('simplify', [status(thm)], ['41'])).
% 0.33/0.52  thf('43', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.33/0.52              (sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.33/0.52             k1_xboole_0)
% 0.33/0.52          | ~ (v1_relat_1 @ X0))),
% 0.33/0.52      inference('eq_fact', [status(thm)], ['42'])).
% 0.33/0.52  thf('44', plain,
% 0.33/0.52      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X6 @ X4)
% 0.33/0.52          | ~ (r2_hidden @ X6 @ X7)
% 0.33/0.52          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.33/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.33/0.52  thf('45', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         (~ (v1_relat_1 @ X0)
% 0.33/0.52          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.33/0.52          | ~ (r1_xboole_0 @ k1_xboole_0 @ X1)
% 0.33/0.52          | ~ (r2_hidden @ 
% 0.33/0.52               (k4_tarski @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.33/0.52                (sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.33/0.52               X1))),
% 0.33/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.33/0.52  thf('46', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 0.33/0.52      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.33/0.52  thf('47', plain,
% 0.33/0.52      (![X4 : $i, X5 : $i]:
% 0.33/0.52         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.33/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.33/0.52  thf('48', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.33/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.33/0.52  thf('49', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         ((r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.33/0.52          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X1))),
% 0.33/0.52      inference('sup-', [status(thm)], ['47', '48'])).
% 0.33/0.52  thf('50', plain,
% 0.33/0.52      (![X4 : $i, X5 : $i]:
% 0.33/0.52         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.33/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.33/0.52  thf('51', plain,
% 0.33/0.52      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X6 @ X4)
% 0.33/0.52          | ~ (r2_hidden @ X6 @ X7)
% 0.33/0.52          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.33/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.33/0.52  thf('52', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.33/0.52         ((r1_xboole_0 @ X0 @ X1)
% 0.33/0.52          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.33/0.52          | ~ (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2))),
% 0.33/0.52      inference('sup-', [status(thm)], ['50', '51'])).
% 0.33/0.52  thf('53', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         ((r1_xboole_0 @ k1_xboole_0 @ X1)
% 0.33/0.52          | ~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.33/0.52          | (r1_xboole_0 @ k1_xboole_0 @ X1))),
% 0.33/0.52      inference('sup-', [status(thm)], ['49', '52'])).
% 0.33/0.52  thf('54', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         (~ (r1_xboole_0 @ k1_xboole_0 @ X0) | (r1_xboole_0 @ k1_xboole_0 @ X1))),
% 0.33/0.52      inference('simplify', [status(thm)], ['53'])).
% 0.33/0.52  thf('55', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.33/0.52      inference('sup-', [status(thm)], ['46', '54'])).
% 0.33/0.52  thf('56', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         (~ (v1_relat_1 @ X0)
% 0.33/0.52          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.33/0.52          | ~ (r2_hidden @ 
% 0.33/0.52               (k4_tarski @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.33/0.52                (sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.33/0.52               X1))),
% 0.33/0.52      inference('demod', [status(thm)], ['45', '55'])).
% 0.33/0.52  thf('57', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.33/0.52              (sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.33/0.52             k1_xboole_0)
% 0.33/0.52          | ~ (v1_relat_1 @ X0))),
% 0.33/0.52      inference('eq_fact', [status(thm)], ['42'])).
% 0.33/0.52  thf('58', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.33/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.33/0.52  thf('59', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         (~ (v1_relat_1 @ X0)
% 0.33/0.52          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.33/0.52              (sk_F @ k1_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.33/0.52             X1))),
% 0.33/0.52      inference('sup-', [status(thm)], ['57', '58'])).
% 0.33/0.52  thf('60', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.33/0.52          | ~ (v1_relat_1 @ X0))),
% 0.33/0.52      inference('clc', [status(thm)], ['56', '59'])).
% 0.33/0.52  thf('61', plain,
% 0.33/0.52      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.33/0.52         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.33/0.52      inference('split', [status(esa)], ['21'])).
% 0.33/0.52  thf('62', plain,
% 0.33/0.52      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.33/0.52         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.33/0.52      inference('sup-', [status(thm)], ['60', '61'])).
% 0.33/0.52  thf('63', plain, ((v1_relat_1 @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('64', plain,
% 0.33/0.52      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.33/0.52         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.33/0.52      inference('demod', [status(thm)], ['62', '63'])).
% 0.33/0.52  thf('65', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.33/0.52      inference('simplify', [status(thm)], ['64'])).
% 0.33/0.52  thf('66', plain,
% 0.33/0.52      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.33/0.52       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.33/0.52      inference('split', [status(esa)], ['21'])).
% 0.33/0.52  thf('67', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.33/0.52      inference('sat_resolution*', [status(thm)], ['65', '66'])).
% 0.33/0.52  thf('68', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.33/0.52      inference('simpl_trail', [status(thm)], ['22', '67'])).
% 0.33/0.52  thf('69', plain,
% 0.33/0.52      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.33/0.52      inference('sup-', [status(thm)], ['20', '68'])).
% 0.33/0.52  thf('70', plain, ((v1_relat_1 @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('71', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.33/0.52      inference('demod', [status(thm)], ['69', '70'])).
% 0.33/0.52  thf('72', plain, ($false), inference('simplify', [status(thm)], ['71'])).
% 0.33/0.52  
% 0.33/0.52  % SZS output end Refutation
% 0.33/0.52  
% 0.33/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

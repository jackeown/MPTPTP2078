%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zn4jQQ4QEd

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:33 EST 2020

% Result     : Theorem 3.35s
% Output     : Refutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 122 expanded)
%              Number of leaves         :   24 (  43 expanded)
%              Depth                    :   17
%              Number of atoms          :  761 (1182 expanded)
%              Number of equality atoms :   50 (  81 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X26 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X27: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X27 ) @ ( sk_C_2 @ X27 ) ) @ X27 )
      | ( X27 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( X19
       != ( k5_relat_1 @ X18 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X23 @ X20 @ X17 @ X18 ) @ X23 ) @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X23 ) @ X19 )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('4',plain,(
    ! [X17: $i,X18: $i,X20: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X23 ) @ ( k5_relat_1 @ X18 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X23 @ X20 @ X17 @ X18 ) @ X23 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ X7 )
      | ( ( k4_xboole_0 @ X5 @ X7 )
       != X5 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

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

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X9 != X8 )
      | ( r2_hidden @ X9 @ X10 )
      | ( X10
       != ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('21',plain,(
    ! [X8: $i] :
      ( r2_hidden @ X8 @ ( k1_tarski @ X8 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

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

thf('29',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('32',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X26 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('33',plain,(
    ! [X27: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X27 ) @ ( sk_C_2 @ X27 ) ) @ X27 )
      | ( X27 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('34',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( X19
       != ( k5_relat_1 @ X18 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ X20 @ ( sk_F_1 @ X23 @ X20 @ X17 @ X18 ) ) @ X18 )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X23 ) @ X19 )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('35',plain,(
    ! [X17: $i,X18: $i,X20: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X23 ) @ ( k5_relat_1 @ X18 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ X20 @ ( sk_F_1 @ X23 @ X20 @ X17 @ X18 ) ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_C_2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','41'])).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('46',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('51',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['49','50'])).

thf('52',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['30','51'])).

thf('53',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference(simplify,[status(thm)],['55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zn4jQQ4QEd
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:50:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 3.35/3.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.35/3.54  % Solved by: fo/fo7.sh
% 3.35/3.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.35/3.54  % done 3813 iterations in 3.081s
% 3.35/3.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.35/3.54  % SZS output start Refutation
% 3.35/3.54  thf(sk_A_type, type, sk_A: $i).
% 3.35/3.54  thf(sk_B_type, type, sk_B: $i > $i).
% 3.35/3.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.35/3.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.35/3.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.35/3.54  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 3.35/3.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.35/3.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.35/3.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.35/3.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.35/3.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.35/3.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.35/3.54  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 3.35/3.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.35/3.54  thf(cc1_relat_1, axiom,
% 3.35/3.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 3.35/3.55  thf('0', plain, (![X16 : $i]: ((v1_relat_1 @ X16) | ~ (v1_xboole_0 @ X16))),
% 3.35/3.55      inference('cnf', [status(esa)], [cc1_relat_1])).
% 3.35/3.55  thf(dt_k5_relat_1, axiom,
% 3.35/3.55    (![A:$i,B:$i]:
% 3.35/3.55     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 3.35/3.55       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 3.35/3.55  thf('1', plain,
% 3.35/3.55      (![X25 : $i, X26 : $i]:
% 3.35/3.55         (~ (v1_relat_1 @ X25)
% 3.35/3.55          | ~ (v1_relat_1 @ X26)
% 3.35/3.55          | (v1_relat_1 @ (k5_relat_1 @ X25 @ X26)))),
% 3.35/3.55      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 3.35/3.55  thf(t56_relat_1, axiom,
% 3.35/3.55    (![A:$i]:
% 3.35/3.55     ( ( v1_relat_1 @ A ) =>
% 3.35/3.55       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 3.35/3.55         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 3.35/3.55  thf('2', plain,
% 3.35/3.55      (![X27 : $i]:
% 3.35/3.55         ((r2_hidden @ (k4_tarski @ (sk_B @ X27) @ (sk_C_2 @ X27)) @ X27)
% 3.35/3.55          | ((X27) = (k1_xboole_0))
% 3.35/3.55          | ~ (v1_relat_1 @ X27))),
% 3.35/3.55      inference('cnf', [status(esa)], [t56_relat_1])).
% 3.35/3.55  thf(d8_relat_1, axiom,
% 3.35/3.55    (![A:$i]:
% 3.35/3.55     ( ( v1_relat_1 @ A ) =>
% 3.35/3.55       ( ![B:$i]:
% 3.35/3.55         ( ( v1_relat_1 @ B ) =>
% 3.35/3.55           ( ![C:$i]:
% 3.35/3.55             ( ( v1_relat_1 @ C ) =>
% 3.35/3.55               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 3.35/3.55                 ( ![D:$i,E:$i]:
% 3.35/3.55                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 3.35/3.55                     ( ?[F:$i]:
% 3.35/3.55                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 3.35/3.55                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 3.35/3.55  thf('3', plain,
% 3.35/3.55      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X23 : $i]:
% 3.35/3.55         (~ (v1_relat_1 @ X17)
% 3.35/3.55          | ((X19) != (k5_relat_1 @ X18 @ X17))
% 3.35/3.55          | (r2_hidden @ 
% 3.35/3.55             (k4_tarski @ (sk_F_1 @ X23 @ X20 @ X17 @ X18) @ X23) @ X17)
% 3.35/3.55          | ~ (r2_hidden @ (k4_tarski @ X20 @ X23) @ X19)
% 3.35/3.55          | ~ (v1_relat_1 @ X19)
% 3.35/3.55          | ~ (v1_relat_1 @ X18))),
% 3.35/3.55      inference('cnf', [status(esa)], [d8_relat_1])).
% 3.35/3.55  thf('4', plain,
% 3.35/3.55      (![X17 : $i, X18 : $i, X20 : $i, X23 : $i]:
% 3.35/3.55         (~ (v1_relat_1 @ X18)
% 3.35/3.55          | ~ (v1_relat_1 @ (k5_relat_1 @ X18 @ X17))
% 3.35/3.55          | ~ (r2_hidden @ (k4_tarski @ X20 @ X23) @ (k5_relat_1 @ X18 @ X17))
% 3.35/3.55          | (r2_hidden @ 
% 3.35/3.55             (k4_tarski @ (sk_F_1 @ X23 @ X20 @ X17 @ X18) @ X23) @ X17)
% 3.35/3.55          | ~ (v1_relat_1 @ X17))),
% 3.35/3.55      inference('simplify', [status(thm)], ['3'])).
% 3.35/3.55  thf('5', plain,
% 3.35/3.55      (![X0 : $i, X1 : $i]:
% 3.35/3.55         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 3.35/3.55          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 3.35/3.55          | ~ (v1_relat_1 @ X0)
% 3.35/3.55          | (r2_hidden @ 
% 3.35/3.55             (k4_tarski @ 
% 3.35/3.55              (sk_F_1 @ (sk_C_2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 3.35/3.55               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 3.35/3.55              (sk_C_2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 3.35/3.55             X0)
% 3.35/3.55          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 3.35/3.55          | ~ (v1_relat_1 @ X1))),
% 3.35/3.55      inference('sup-', [status(thm)], ['2', '4'])).
% 3.35/3.55  thf('6', plain,
% 3.35/3.55      (![X0 : $i, X1 : $i]:
% 3.35/3.55         (~ (v1_relat_1 @ X1)
% 3.35/3.55          | (r2_hidden @ 
% 3.35/3.55             (k4_tarski @ 
% 3.35/3.55              (sk_F_1 @ (sk_C_2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 3.35/3.55               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 3.35/3.55              (sk_C_2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 3.35/3.55             X0)
% 3.35/3.55          | ~ (v1_relat_1 @ X0)
% 3.35/3.55          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 3.35/3.55          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 3.35/3.55      inference('simplify', [status(thm)], ['5'])).
% 3.35/3.55  thf('7', plain,
% 3.35/3.55      (![X0 : $i, X1 : $i]:
% 3.35/3.55         (~ (v1_relat_1 @ X0)
% 3.35/3.55          | ~ (v1_relat_1 @ X1)
% 3.35/3.55          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 3.35/3.55          | ~ (v1_relat_1 @ X0)
% 3.35/3.55          | (r2_hidden @ 
% 3.35/3.55             (k4_tarski @ 
% 3.35/3.55              (sk_F_1 @ (sk_C_2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 3.35/3.55               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 3.35/3.55              (sk_C_2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 3.35/3.55             X0)
% 3.35/3.55          | ~ (v1_relat_1 @ X1))),
% 3.35/3.55      inference('sup-', [status(thm)], ['1', '6'])).
% 3.35/3.55  thf('8', plain,
% 3.35/3.55      (![X0 : $i, X1 : $i]:
% 3.35/3.55         ((r2_hidden @ 
% 3.35/3.55           (k4_tarski @ 
% 3.35/3.55            (sk_F_1 @ (sk_C_2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 3.35/3.55             (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 3.35/3.55            (sk_C_2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 3.35/3.55           X0)
% 3.35/3.55          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 3.35/3.55          | ~ (v1_relat_1 @ X1)
% 3.35/3.55          | ~ (v1_relat_1 @ X0))),
% 3.35/3.55      inference('simplify', [status(thm)], ['7'])).
% 3.35/3.55  thf(t4_boole, axiom,
% 3.35/3.55    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 3.35/3.55  thf('9', plain,
% 3.35/3.55      (![X4 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 3.35/3.55      inference('cnf', [status(esa)], [t4_boole])).
% 3.35/3.55  thf(t83_xboole_1, axiom,
% 3.35/3.55    (![A:$i,B:$i]:
% 3.35/3.55     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.35/3.55  thf('10', plain,
% 3.35/3.55      (![X5 : $i, X7 : $i]:
% 3.35/3.55         ((r1_xboole_0 @ X5 @ X7) | ((k4_xboole_0 @ X5 @ X7) != (X5)))),
% 3.35/3.55      inference('cnf', [status(esa)], [t83_xboole_1])).
% 3.35/3.55  thf('11', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 3.35/3.55      inference('sup-', [status(thm)], ['9', '10'])).
% 3.35/3.55  thf('12', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 3.35/3.55      inference('simplify', [status(thm)], ['11'])).
% 3.35/3.55  thf(t3_xboole_0, axiom,
% 3.35/3.55    (![A:$i,B:$i]:
% 3.35/3.55     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 3.35/3.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 3.35/3.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 3.35/3.55            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 3.35/3.55  thf('13', plain,
% 3.35/3.55      (![X0 : $i, X1 : $i]:
% 3.35/3.55         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 3.35/3.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.35/3.55  thf('14', plain,
% 3.35/3.55      (![X0 : $i, X1 : $i]:
% 3.35/3.55         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 3.35/3.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.35/3.55  thf('15', plain,
% 3.35/3.55      (![X0 : $i, X2 : $i, X3 : $i]:
% 3.35/3.55         (~ (r2_hidden @ X2 @ X0)
% 3.35/3.55          | ~ (r2_hidden @ X2 @ X3)
% 3.35/3.55          | ~ (r1_xboole_0 @ X0 @ X3))),
% 3.35/3.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.35/3.55  thf('16', plain,
% 3.35/3.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.35/3.55         ((r1_xboole_0 @ X1 @ X0)
% 3.35/3.55          | ~ (r1_xboole_0 @ X0 @ X2)
% 3.35/3.55          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 3.35/3.55      inference('sup-', [status(thm)], ['14', '15'])).
% 3.35/3.55  thf('17', plain,
% 3.35/3.55      (![X0 : $i, X1 : $i]:
% 3.35/3.55         ((r1_xboole_0 @ X0 @ X1)
% 3.35/3.55          | ~ (r1_xboole_0 @ X1 @ X0)
% 3.35/3.55          | (r1_xboole_0 @ X0 @ X1))),
% 3.35/3.55      inference('sup-', [status(thm)], ['13', '16'])).
% 3.35/3.55  thf('18', plain,
% 3.35/3.55      (![X0 : $i, X1 : $i]:
% 3.35/3.55         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 3.35/3.55      inference('simplify', [status(thm)], ['17'])).
% 3.35/3.55  thf('19', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 3.35/3.55      inference('sup-', [status(thm)], ['12', '18'])).
% 3.35/3.55  thf(d1_tarski, axiom,
% 3.35/3.55    (![A:$i,B:$i]:
% 3.35/3.55     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 3.35/3.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 3.35/3.55  thf('20', plain,
% 3.35/3.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.35/3.55         (((X9) != (X8)) | (r2_hidden @ X9 @ X10) | ((X10) != (k1_tarski @ X8)))),
% 3.35/3.55      inference('cnf', [status(esa)], [d1_tarski])).
% 3.35/3.55  thf('21', plain, (![X8 : $i]: (r2_hidden @ X8 @ (k1_tarski @ X8))),
% 3.35/3.55      inference('simplify', [status(thm)], ['20'])).
% 3.35/3.55  thf('22', plain,
% 3.35/3.55      (![X0 : $i, X2 : $i, X3 : $i]:
% 3.35/3.55         (~ (r2_hidden @ X2 @ X0)
% 3.35/3.55          | ~ (r2_hidden @ X2 @ X3)
% 3.35/3.55          | ~ (r1_xboole_0 @ X0 @ X3))),
% 3.35/3.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.35/3.55  thf('23', plain,
% 3.35/3.55      (![X0 : $i, X1 : $i]:
% 3.35/3.55         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 3.35/3.55      inference('sup-', [status(thm)], ['21', '22'])).
% 3.35/3.55  thf('24', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.35/3.55      inference('sup-', [status(thm)], ['19', '23'])).
% 3.35/3.55  thf('25', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         (~ (v1_relat_1 @ k1_xboole_0)
% 3.35/3.55          | ~ (v1_relat_1 @ X0)
% 3.35/3.55          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 3.35/3.55      inference('sup-', [status(thm)], ['8', '24'])).
% 3.35/3.55  thf('26', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.35/3.55          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 3.35/3.55          | ~ (v1_relat_1 @ X0))),
% 3.35/3.55      inference('sup-', [status(thm)], ['0', '25'])).
% 3.35/3.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.35/3.55  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.35/3.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.35/3.55  thf('28', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         (((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 3.35/3.55          | ~ (v1_relat_1 @ X0))),
% 3.35/3.55      inference('demod', [status(thm)], ['26', '27'])).
% 3.35/3.55  thf(t62_relat_1, conjecture,
% 3.35/3.55    (![A:$i]:
% 3.35/3.55     ( ( v1_relat_1 @ A ) =>
% 3.35/3.55       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 3.35/3.55         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 3.35/3.55  thf(zf_stmt_0, negated_conjecture,
% 3.35/3.55    (~( ![A:$i]:
% 3.35/3.55        ( ( v1_relat_1 @ A ) =>
% 3.35/3.55          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 3.35/3.55            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 3.35/3.55    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 3.35/3.55  thf('29', plain,
% 3.35/3.55      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 3.35/3.55        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('30', plain,
% 3.35/3.55      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 3.35/3.55         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 3.35/3.55      inference('split', [status(esa)], ['29'])).
% 3.35/3.55  thf('31', plain, (![X16 : $i]: ((v1_relat_1 @ X16) | ~ (v1_xboole_0 @ X16))),
% 3.35/3.55      inference('cnf', [status(esa)], [cc1_relat_1])).
% 3.35/3.55  thf('32', plain,
% 3.35/3.55      (![X25 : $i, X26 : $i]:
% 3.35/3.55         (~ (v1_relat_1 @ X25)
% 3.35/3.55          | ~ (v1_relat_1 @ X26)
% 3.35/3.55          | (v1_relat_1 @ (k5_relat_1 @ X25 @ X26)))),
% 3.35/3.55      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 3.35/3.55  thf('33', plain,
% 3.35/3.55      (![X27 : $i]:
% 3.35/3.55         ((r2_hidden @ (k4_tarski @ (sk_B @ X27) @ (sk_C_2 @ X27)) @ X27)
% 3.35/3.55          | ((X27) = (k1_xboole_0))
% 3.35/3.55          | ~ (v1_relat_1 @ X27))),
% 3.35/3.55      inference('cnf', [status(esa)], [t56_relat_1])).
% 3.35/3.55  thf('34', plain,
% 3.35/3.55      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X23 : $i]:
% 3.35/3.55         (~ (v1_relat_1 @ X17)
% 3.35/3.55          | ((X19) != (k5_relat_1 @ X18 @ X17))
% 3.35/3.55          | (r2_hidden @ 
% 3.35/3.55             (k4_tarski @ X20 @ (sk_F_1 @ X23 @ X20 @ X17 @ X18)) @ X18)
% 3.35/3.55          | ~ (r2_hidden @ (k4_tarski @ X20 @ X23) @ X19)
% 3.35/3.55          | ~ (v1_relat_1 @ X19)
% 3.35/3.55          | ~ (v1_relat_1 @ X18))),
% 3.35/3.55      inference('cnf', [status(esa)], [d8_relat_1])).
% 3.35/3.55  thf('35', plain,
% 3.35/3.55      (![X17 : $i, X18 : $i, X20 : $i, X23 : $i]:
% 3.35/3.55         (~ (v1_relat_1 @ X18)
% 3.35/3.55          | ~ (v1_relat_1 @ (k5_relat_1 @ X18 @ X17))
% 3.35/3.55          | ~ (r2_hidden @ (k4_tarski @ X20 @ X23) @ (k5_relat_1 @ X18 @ X17))
% 3.35/3.55          | (r2_hidden @ 
% 3.35/3.55             (k4_tarski @ X20 @ (sk_F_1 @ X23 @ X20 @ X17 @ X18)) @ X18)
% 3.35/3.55          | ~ (v1_relat_1 @ X17))),
% 3.35/3.55      inference('simplify', [status(thm)], ['34'])).
% 3.35/3.55  thf('36', plain,
% 3.35/3.55      (![X0 : $i, X1 : $i]:
% 3.35/3.55         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 3.35/3.55          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 3.35/3.55          | ~ (v1_relat_1 @ X0)
% 3.35/3.55          | (r2_hidden @ 
% 3.35/3.55             (k4_tarski @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ 
% 3.35/3.55              (sk_F_1 @ (sk_C_2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 3.35/3.55               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 3.35/3.55             X1)
% 3.35/3.55          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 3.35/3.55          | ~ (v1_relat_1 @ X1))),
% 3.35/3.55      inference('sup-', [status(thm)], ['33', '35'])).
% 3.35/3.55  thf('37', plain,
% 3.35/3.55      (![X0 : $i, X1 : $i]:
% 3.35/3.55         (~ (v1_relat_1 @ X1)
% 3.35/3.55          | (r2_hidden @ 
% 3.35/3.55             (k4_tarski @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ 
% 3.35/3.55              (sk_F_1 @ (sk_C_2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 3.35/3.55               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 3.35/3.55             X1)
% 3.35/3.55          | ~ (v1_relat_1 @ X0)
% 3.35/3.55          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 3.35/3.55          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 3.35/3.55      inference('simplify', [status(thm)], ['36'])).
% 3.35/3.55  thf('38', plain,
% 3.35/3.55      (![X0 : $i, X1 : $i]:
% 3.35/3.55         (~ (v1_relat_1 @ X0)
% 3.35/3.55          | ~ (v1_relat_1 @ X1)
% 3.35/3.55          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 3.35/3.55          | ~ (v1_relat_1 @ X0)
% 3.35/3.55          | (r2_hidden @ 
% 3.35/3.55             (k4_tarski @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ 
% 3.35/3.55              (sk_F_1 @ (sk_C_2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 3.35/3.55               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 3.35/3.55             X1)
% 3.35/3.55          | ~ (v1_relat_1 @ X1))),
% 3.35/3.55      inference('sup-', [status(thm)], ['32', '37'])).
% 3.35/3.55  thf('39', plain,
% 3.35/3.55      (![X0 : $i, X1 : $i]:
% 3.35/3.55         ((r2_hidden @ 
% 3.35/3.55           (k4_tarski @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ 
% 3.35/3.55            (sk_F_1 @ (sk_C_2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 3.35/3.55             (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 3.35/3.55           X1)
% 3.35/3.55          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 3.35/3.55          | ~ (v1_relat_1 @ X1)
% 3.35/3.55          | ~ (v1_relat_1 @ X0))),
% 3.35/3.55      inference('simplify', [status(thm)], ['38'])).
% 3.35/3.55  thf('40', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.35/3.55      inference('sup-', [status(thm)], ['19', '23'])).
% 3.35/3.55  thf('41', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         (~ (v1_relat_1 @ X0)
% 3.35/3.55          | ~ (v1_relat_1 @ k1_xboole_0)
% 3.35/3.55          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 3.35/3.55      inference('sup-', [status(thm)], ['39', '40'])).
% 3.35/3.55  thf('42', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.35/3.55          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 3.35/3.55          | ~ (v1_relat_1 @ X0))),
% 3.35/3.55      inference('sup-', [status(thm)], ['31', '41'])).
% 3.35/3.55  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.35/3.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.35/3.55  thf('44', plain,
% 3.35/3.55      (![X0 : $i]:
% 3.35/3.55         (((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 3.35/3.55          | ~ (v1_relat_1 @ X0))),
% 3.35/3.55      inference('demod', [status(thm)], ['42', '43'])).
% 3.35/3.55  thf('45', plain,
% 3.35/3.55      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 3.35/3.55         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 3.35/3.55      inference('split', [status(esa)], ['29'])).
% 3.35/3.55  thf('46', plain,
% 3.35/3.55      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 3.35/3.55         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 3.35/3.55      inference('sup-', [status(thm)], ['44', '45'])).
% 3.35/3.55  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('48', plain,
% 3.35/3.55      ((((k1_xboole_0) != (k1_xboole_0)))
% 3.35/3.55         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 3.35/3.55      inference('demod', [status(thm)], ['46', '47'])).
% 3.35/3.55  thf('49', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 3.35/3.55      inference('simplify', [status(thm)], ['48'])).
% 3.35/3.55  thf('50', plain,
% 3.35/3.55      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 3.35/3.55       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 3.35/3.55      inference('split', [status(esa)], ['29'])).
% 3.35/3.55  thf('51', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 3.35/3.55      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 3.35/3.55  thf('52', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 3.35/3.55      inference('simpl_trail', [status(thm)], ['30', '51'])).
% 3.35/3.55  thf('53', plain,
% 3.35/3.55      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 3.35/3.55      inference('sup-', [status(thm)], ['28', '52'])).
% 3.35/3.55  thf('54', plain, ((v1_relat_1 @ sk_A)),
% 3.35/3.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.55  thf('55', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 3.35/3.55      inference('demod', [status(thm)], ['53', '54'])).
% 3.35/3.55  thf('56', plain, ($false), inference('simplify', [status(thm)], ['55'])).
% 3.35/3.55  
% 3.35/3.55  % SZS output end Refutation
% 3.35/3.55  
% 3.35/3.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

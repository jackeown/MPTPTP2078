%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FHsiJ7KPzx

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 (  82 expanded)
%              Number of leaves         :   16 (  29 expanded)
%              Depth                    :   20
%              Number of atoms          :  955 (1253 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   21 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X4 @ X5 ) @ ( sk_D @ X4 @ X5 ) ) @ X5 )
      | ( r1_tarski @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

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
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( X11
       != ( k5_relat_1 @ X10 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ X12 @ ( sk_F_1 @ X15 @ X12 @ X9 @ X10 ) ) @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X15 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('4',plain,(
    ! [X9: $i,X10: $i,X12: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X15 ) @ ( k5_relat_1 @ X10 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ X12 @ ( sk_F_1 @ X15 @ X12 @ X9 @ X10 ) ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X4 @ X5 ) @ ( sk_D @ X4 @ X5 ) ) @ X5 )
      | ( r1_tarski @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( X11
       != ( k5_relat_1 @ X10 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X15 @ X12 @ X9 @ X10 ) @ X15 ) @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X15 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('12',plain,(
    ! [X9: $i,X10: $i,X12: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X15 ) @ ( k5_relat_1 @ X10 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X15 @ X12 @ X9 @ X10 ) @ X15 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t48_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( r1_tarski @ A @ B )
               => ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( ( r1_tarski @ A @ B )
                 => ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_relat_1])).

thf('17',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ ( sk_C_1 @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ sk_A @ X0 ) @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ ( sk_C_1 @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ sk_A @ X0 ) @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( X11
       != ( k5_relat_1 @ X10 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X13 ) @ X9 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('25',plain,(
    ! [X9: $i,X10: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X13 ) @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ ( k5_relat_1 @ X10 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) ) @ ( k5_relat_1 @ X2 @ sk_B ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_F_1 @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ ( sk_C_1 @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ sk_A @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) ) @ ( k5_relat_1 @ X2 @ sk_B ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_F_1 @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ ( sk_C_1 @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ sk_A @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) ) @ ( k5_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) ) @ ( k5_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) ) @ ( k5_relat_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X4 @ X5 ) @ ( sk_D @ X4 @ X5 ) ) @ X4 )
      | ( r1_tarski @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ ( k5_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ ( k5_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ ( k5_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ ( k5_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ ( k5_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ ( k5_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_C_2 @ sk_A ) @ ( k5_relat_1 @ sk_C_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['43','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FHsiJ7KPzx
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 79 iterations in 0.062s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.51  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.51  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(dt_k5_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.51       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X17)
% 0.21/0.51          | ~ (v1_relat_1 @ X18)
% 0.21/0.51          | (v1_relat_1 @ (k5_relat_1 @ X17 @ X18)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X17)
% 0.21/0.51          | ~ (v1_relat_1 @ X18)
% 0.21/0.51          | (v1_relat_1 @ (k5_relat_1 @ X17 @ X18)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.51  thf(d3_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.51           ( ![C:$i,D:$i]:
% 0.21/0.51             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.21/0.51               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         ((r2_hidden @ (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ X5)
% 0.21/0.51          | (r1_tarski @ X5 @ X4)
% 0.21/0.51          | ~ (v1_relat_1 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.51  thf(d8_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( v1_relat_1 @ B ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( v1_relat_1 @ C ) =>
% 0.21/0.51               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 0.21/0.51                 ( ![D:$i,E:$i]:
% 0.21/0.51                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.21/0.51                     ( ?[F:$i]:
% 0.21/0.51                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 0.21/0.51                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X15 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X9)
% 0.21/0.51          | ((X11) != (k5_relat_1 @ X10 @ X9))
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X12 @ (sk_F_1 @ X15 @ X12 @ X9 @ X10)) @ 
% 0.21/0.51             X10)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X12 @ X15) @ X11)
% 0.21/0.51          | ~ (v1_relat_1 @ X11)
% 0.21/0.51          | ~ (v1_relat_1 @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X12 : $i, X15 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X10)
% 0.21/0.51          | ~ (v1_relat_1 @ (k5_relat_1 @ X10 @ X9))
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X12 @ X15) @ (k5_relat_1 @ X10 @ X9))
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X12 @ (sk_F_1 @ X15 @ X12 @ X9 @ X10)) @ 
% 0.21/0.51             X10)
% 0.21/0.51          | ~ (v1_relat_1 @ X9))),
% 0.21/0.51      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.51          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.51              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.51               (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 0.21/0.51             X1)
% 0.21/0.51          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '4'])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X1)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.51              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.51               (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 0.21/0.51             X1)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.51          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X1)
% 0.21/0.51          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.51              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.51               (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 0.21/0.51             X1)
% 0.21/0.51          | ~ (v1_relat_1 @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '6'])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((r2_hidden @ 
% 0.21/0.51           (k4_tarski @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.51            (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.51             (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 0.21/0.51           X1)
% 0.21/0.51          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.51          | ~ (v1_relat_1 @ X1)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X17)
% 0.21/0.51          | ~ (v1_relat_1 @ X18)
% 0.21/0.51          | (v1_relat_1 @ (k5_relat_1 @ X17 @ X18)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         ((r2_hidden @ (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ X5)
% 0.21/0.51          | (r1_tarski @ X5 @ X4)
% 0.21/0.51          | ~ (v1_relat_1 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X15 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X9)
% 0.21/0.51          | ((X11) != (k5_relat_1 @ X10 @ X9))
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ (sk_F_1 @ X15 @ X12 @ X9 @ X10) @ X15) @ 
% 0.21/0.51             X9)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X12 @ X15) @ X11)
% 0.21/0.51          | ~ (v1_relat_1 @ X11)
% 0.21/0.51          | ~ (v1_relat_1 @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X12 : $i, X15 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X10)
% 0.21/0.51          | ~ (v1_relat_1 @ (k5_relat_1 @ X10 @ X9))
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X12 @ X15) @ (k5_relat_1 @ X10 @ X9))
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ (sk_F_1 @ X15 @ X12 @ X9 @ X10) @ X15) @ 
% 0.21/0.51             X9)
% 0.21/0.51          | ~ (v1_relat_1 @ X9))),
% 0.21/0.51      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.51          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ 
% 0.21/0.51              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.51               (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.21/0.51              (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.21/0.51             X0)
% 0.21/0.51          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X1)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ 
% 0.21/0.51              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.51               (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.21/0.51              (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.21/0.51             X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.51          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X1)
% 0.21/0.51          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ 
% 0.21/0.51              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.51               (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.21/0.51              (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.21/0.51             X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((r2_hidden @ 
% 0.21/0.51           (k4_tarski @ 
% 0.21/0.51            (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.51             (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.21/0.51            (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.21/0.51           X0)
% 0.21/0.51          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.51          | ~ (v1_relat_1 @ X1)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.51  thf(t48_relat_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( v1_relat_1 @ B ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( v1_relat_1 @ C ) =>
% 0.21/0.51               ( ( r1_tarski @ A @ B ) =>
% 0.21/0.51                 ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( v1_relat_1 @ A ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( v1_relat_1 @ B ) =>
% 0.21/0.51              ( ![C:$i]:
% 0.21/0.51                ( ( v1_relat_1 @ C ) =>
% 0.21/0.51                  ( ( r1_tarski @ A @ B ) =>
% 0.21/0.51                    ( r1_tarski @
% 0.21/0.51                      ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t48_relat_1])).
% 0.21/0.51  thf('17', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d3_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.51          | (r2_hidden @ X0 @ X2)
% 0.21/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ sk_A)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r1_tarski @ (k5_relat_1 @ X0 @ sk_A) @ X1)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ 
% 0.21/0.51              (sk_F_1 @ (sk_D @ X1 @ (k5_relat_1 @ X0 @ sk_A)) @ 
% 0.21/0.51               (sk_C_1 @ X1 @ (k5_relat_1 @ X0 @ sk_A)) @ sk_A @ X0) @ 
% 0.21/0.51              (sk_D @ X1 @ (k5_relat_1 @ X0 @ sk_A))) @ 
% 0.21/0.51             sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '19'])).
% 0.21/0.51  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r1_tarski @ (k5_relat_1 @ X0 @ sk_A) @ X1)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ 
% 0.21/0.51              (sk_F_1 @ (sk_D @ X1 @ (k5_relat_1 @ X0 @ sk_A)) @ 
% 0.21/0.51               (sk_C_1 @ X1 @ (k5_relat_1 @ X0 @ sk_A)) @ sk_A @ X0) @ 
% 0.21/0.51              (sk_D @ X1 @ (k5_relat_1 @ X0 @ sk_A))) @ 
% 0.21/0.51             sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X17)
% 0.21/0.51          | ~ (v1_relat_1 @ X18)
% 0.21/0.51          | (v1_relat_1 @ (k5_relat_1 @ X17 @ X18)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X9)
% 0.21/0.51          | ((X11) != (k5_relat_1 @ X10 @ X9))
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X12 @ X13) @ X11)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ X10)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X14 @ X13) @ X9)
% 0.21/0.51          | ~ (v1_relat_1 @ X11)
% 0.21/0.51          | ~ (v1_relat_1 @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X10)
% 0.21/0.51          | ~ (v1_relat_1 @ (k5_relat_1 @ X10 @ X9))
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X14 @ X13) @ X9)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ X10)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X12 @ X13) @ (k5_relat_1 @ X10 @ X9))
% 0.21/0.51          | ~ (v1_relat_1 @ X9))),
% 0.21/0.51      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X1)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         (~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X1)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((r1_tarski @ (k5_relat_1 @ X0 @ sk_A) @ X1)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ sk_B)
% 0.21/0.51          | ~ (v1_relat_1 @ X2)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ X3 @ (sk_D @ X1 @ (k5_relat_1 @ X0 @ sk_A))) @ 
% 0.21/0.51             (k5_relat_1 @ X2 @ sk_B))
% 0.21/0.51          | ~ (r2_hidden @ 
% 0.21/0.51               (k4_tarski @ X3 @ 
% 0.21/0.51                (sk_F_1 @ (sk_D @ X1 @ (k5_relat_1 @ X0 @ sk_A)) @ 
% 0.21/0.51                 (sk_C_1 @ X1 @ (k5_relat_1 @ X0 @ sk_A)) @ sk_A @ X0)) @ 
% 0.21/0.51               X2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['22', '27'])).
% 0.21/0.51  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((r1_tarski @ (k5_relat_1 @ X0 @ sk_A) @ X1)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X2)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ X3 @ (sk_D @ X1 @ (k5_relat_1 @ X0 @ sk_A))) @ 
% 0.21/0.51             (k5_relat_1 @ X2 @ sk_B))
% 0.21/0.51          | ~ (r2_hidden @ 
% 0.21/0.51               (k4_tarski @ X3 @ 
% 0.21/0.51                (sk_F_1 @ (sk_D @ X1 @ (k5_relat_1 @ X0 @ sk_A)) @ 
% 0.21/0.51                 (sk_C_1 @ X1 @ (k5_relat_1 @ X0 @ sk_A)) @ sk_A @ X0)) @ 
% 0.21/0.51               X2))),
% 0.21/0.51      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ sk_A)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r1_tarski @ (k5_relat_1 @ X0 @ sk_A) @ X1)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C_1 @ X1 @ (k5_relat_1 @ X0 @ sk_A)) @ 
% 0.21/0.51              (sk_D @ X1 @ (k5_relat_1 @ X0 @ sk_A))) @ 
% 0.21/0.51             (k5_relat_1 @ X0 @ sk_B))
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r1_tarski @ (k5_relat_1 @ X0 @ sk_A) @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '30'])).
% 0.21/0.51  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r1_tarski @ (k5_relat_1 @ X0 @ sk_A) @ X1)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C_1 @ X1 @ (k5_relat_1 @ X0 @ sk_A)) @ 
% 0.21/0.51              (sk_D @ X1 @ (k5_relat_1 @ X0 @ sk_A))) @ 
% 0.21/0.51             (k5_relat_1 @ X0 @ sk_B))
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r1_tarski @ (k5_relat_1 @ X0 @ sk_A) @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r2_hidden @ 
% 0.21/0.51           (k4_tarski @ (sk_C_1 @ X1 @ (k5_relat_1 @ X0 @ sk_A)) @ 
% 0.21/0.51            (sk_D @ X1 @ (k5_relat_1 @ X0 @ sk_A))) @ 
% 0.21/0.51           (k5_relat_1 @ X0 @ sk_B))
% 0.21/0.51          | (r1_tarski @ (k5_relat_1 @ X0 @ sk_A) @ X1)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         (~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_D @ X4 @ X5)) @ 
% 0.21/0.51             X4)
% 0.21/0.51          | (r1_tarski @ X5 @ X4)
% 0.21/0.51          | ~ (v1_relat_1 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r1_tarski @ (k5_relat_1 @ X0 @ sk_A) @ (k5_relat_1 @ X0 @ sk_B))
% 0.21/0.51          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.21/0.51          | (r1_tarski @ (k5_relat_1 @ X0 @ sk_A) @ (k5_relat_1 @ X0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ (k5_relat_1 @ X0 @ sk_A))
% 0.21/0.51          | (r1_tarski @ (k5_relat_1 @ X0 @ sk_A) @ (k5_relat_1 @ X0 @ sk_B))
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ sk_A)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r1_tarski @ (k5_relat_1 @ X0 @ sk_A) @ (k5_relat_1 @ X0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '37'])).
% 0.21/0.51  thf('39', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r1_tarski @ (k5_relat_1 @ X0 @ sk_A) @ (k5_relat_1 @ X0 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r1_tarski @ (k5_relat_1 @ X0 @ sk_A) @ (k5_relat_1 @ X0 @ sk_B))
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (~ (r1_tarski @ (k5_relat_1 @ sk_C_2 @ sk_A) @ 
% 0.21/0.51          (k5_relat_1 @ sk_C_2 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('43', plain, (~ (v1_relat_1 @ sk_C_2)),
% 0.21/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.51  thf('44', plain, ((v1_relat_1 @ sk_C_2)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('45', plain, ($false), inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

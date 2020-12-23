%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3FbtoUS4Fp

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:07 EST 2020

% Result     : Theorem 3.35s
% Output     : Refutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 120 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :   24
%              Number of atoms          : 1053 (1540 expanded)
%              Number of equality atoms :   27 (  56 expanded)
%              Maximal formula depth    :   18 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_relat_1 @ X27 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

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

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( X20
       != ( k5_relat_1 @ X19 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ X21 @ ( sk_F_1 @ X24 @ X21 @ X18 @ X19 ) ) @ X19 )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X24 ) @ X20 )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('3',plain,(
    ! [X18: $i,X19: $i,X21: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X18 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X24 ) @ ( k5_relat_1 @ X19 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ X21 @ ( sk_F_1 @ X24 @ X21 @ X18 @ X19 ) ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k1_relat_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(eq_fact,[status(thm)],['9'])).

thf('11',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9
        = ( k1_relat_1 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X9 @ X6 ) @ ( sk_D @ X9 @ X6 ) ) @ X6 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X6 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D_1 @ X8 @ X6 ) ) @ X6 )
      | ( X7
       != ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('16',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D_1 @ X8 @ X6 ) ) @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X13 )
      | ( r2_hidden @ X12 @ X14 )
      | ( X14
       != ( k2_relat_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ ( k2_relat_1 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X13 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf(t46_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
             => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
                = ( k1_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_relat_1])).

thf('22',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_A ) ) @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D_1 @ X8 @ X6 ) ) @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_A ) ) @ sk_A ) @ ( sk_D_1 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_A ) ) @ sk_A ) @ sk_B ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_relat_1 @ X27 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('29',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( X20
       != ( k5_relat_1 @ X19 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ X21 @ X22 ) @ X20 )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ X19 )
      | ~ ( r2_hidden @ ( k4_tarski @ X23 @ X22 ) @ X18 )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('30',plain,(
    ! [X18: $i,X19: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X18 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X23 @ X22 ) @ X18 )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ X19 )
      | ( r2_hidden @ ( k4_tarski @ X21 @ X22 ) @ ( k5_relat_1 @ X19 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_D_1 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_A ) ) @ sk_A ) @ sk_B ) ) @ ( k5_relat_1 @ X1 @ sk_B ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_A ) ) @ sk_A ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_D_1 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_A ) ) @ sk_A ) @ sk_B ) ) @ ( k5_relat_1 @ X1 @ sk_B ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_A ) ) @ sk_A ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_A ) ) @ ( sk_D_1 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_A ) ) @ sk_A ) @ sk_B ) ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_A ) ) @ ( sk_D_1 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_A ) ) @ sk_A ) @ sk_B ) ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_A ) ) @ ( sk_D_1 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_A ) ) @ sk_A ) @ sk_B ) ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ sk_A )
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['13','46'])).

thf('48',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r2_hidden @ ( sk_C_1 @ ( k1_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(eq_fact,[status(thm)],['47'])).

thf('49',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
 != ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r2_hidden @ ( sk_C_1 @ ( k1_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D_1 @ X8 @ X6 ) ) @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('52',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( k1_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) ) @ ( sk_D_1 @ ( sk_C_1 @ ( k1_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) ) @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) @ ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X6: $i,X9: $i,X10: $i] :
      ( ( X9
        = ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X9 @ X6 ) @ X10 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X9 @ X6 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('54',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ ( k1_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) ) @ ( k1_relat_1 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_A )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
 != ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ~ ( r2_hidden @ ( sk_C_1 @ ( k1_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A )
    | ( ( k1_relat_1 @ sk_A )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
 != ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['60','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3FbtoUS4Fp
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:39:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.35/3.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.35/3.60  % Solved by: fo/fo7.sh
% 3.35/3.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.35/3.60  % done 3187 iterations in 3.140s
% 3.35/3.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.35/3.60  % SZS output start Refutation
% 3.35/3.60  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.35/3.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.35/3.60  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 3.35/3.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.35/3.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.35/3.60  thf(sk_B_type, type, sk_B: $i).
% 3.35/3.60  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.35/3.60  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 3.35/3.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.35/3.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.35/3.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.35/3.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.35/3.60  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 3.35/3.60  thf(sk_A_type, type, sk_A: $i).
% 3.35/3.60  thf(dt_k5_relat_1, axiom,
% 3.35/3.60    (![A:$i,B:$i]:
% 3.35/3.60     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 3.35/3.60       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 3.35/3.60  thf('0', plain,
% 3.35/3.60      (![X26 : $i, X27 : $i]:
% 3.35/3.60         (~ (v1_relat_1 @ X26)
% 3.35/3.60          | ~ (v1_relat_1 @ X27)
% 3.35/3.60          | (v1_relat_1 @ (k5_relat_1 @ X26 @ X27)))),
% 3.35/3.60      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 3.35/3.60  thf(d4_relat_1, axiom,
% 3.35/3.60    (![A:$i,B:$i]:
% 3.35/3.60     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 3.35/3.60       ( ![C:$i]:
% 3.35/3.60         ( ( r2_hidden @ C @ B ) <=>
% 3.35/3.60           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 3.35/3.60  thf('1', plain,
% 3.35/3.60      (![X6 : $i, X9 : $i]:
% 3.35/3.60         (((X9) = (k1_relat_1 @ X6))
% 3.35/3.60          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X9 @ X6) @ (sk_D @ X9 @ X6)) @ 
% 3.35/3.60             X6)
% 3.35/3.60          | (r2_hidden @ (sk_C_1 @ X9 @ X6) @ X9))),
% 3.35/3.60      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.35/3.60  thf(d8_relat_1, axiom,
% 3.35/3.60    (![A:$i]:
% 3.35/3.60     ( ( v1_relat_1 @ A ) =>
% 3.35/3.60       ( ![B:$i]:
% 3.35/3.60         ( ( v1_relat_1 @ B ) =>
% 3.35/3.60           ( ![C:$i]:
% 3.35/3.60             ( ( v1_relat_1 @ C ) =>
% 3.35/3.60               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 3.35/3.60                 ( ![D:$i,E:$i]:
% 3.35/3.60                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 3.35/3.60                     ( ?[F:$i]:
% 3.35/3.60                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 3.35/3.60                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 3.35/3.60  thf('2', plain,
% 3.35/3.60      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X24 : $i]:
% 3.35/3.60         (~ (v1_relat_1 @ X18)
% 3.35/3.60          | ((X20) != (k5_relat_1 @ X19 @ X18))
% 3.35/3.60          | (r2_hidden @ 
% 3.35/3.60             (k4_tarski @ X21 @ (sk_F_1 @ X24 @ X21 @ X18 @ X19)) @ X19)
% 3.35/3.60          | ~ (r2_hidden @ (k4_tarski @ X21 @ X24) @ X20)
% 3.35/3.60          | ~ (v1_relat_1 @ X20)
% 3.35/3.60          | ~ (v1_relat_1 @ X19))),
% 3.35/3.60      inference('cnf', [status(esa)], [d8_relat_1])).
% 3.35/3.60  thf('3', plain,
% 3.35/3.60      (![X18 : $i, X19 : $i, X21 : $i, X24 : $i]:
% 3.35/3.60         (~ (v1_relat_1 @ X19)
% 3.35/3.60          | ~ (v1_relat_1 @ (k5_relat_1 @ X19 @ X18))
% 3.35/3.60          | ~ (r2_hidden @ (k4_tarski @ X21 @ X24) @ (k5_relat_1 @ X19 @ X18))
% 3.35/3.60          | (r2_hidden @ 
% 3.35/3.60             (k4_tarski @ X21 @ (sk_F_1 @ X24 @ X21 @ X18 @ X19)) @ X19)
% 3.35/3.60          | ~ (v1_relat_1 @ X18))),
% 3.35/3.60      inference('simplify', [status(thm)], ['2'])).
% 3.35/3.60  thf('4', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.35/3.60         ((r2_hidden @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X2)
% 3.35/3.60          | ((X2) = (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 3.35/3.60          | ~ (v1_relat_1 @ X0)
% 3.35/3.60          | (r2_hidden @ 
% 3.35/3.60             (k4_tarski @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 3.35/3.60              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 3.35/3.60               (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 3.35/3.60             X1)
% 3.35/3.60          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 3.35/3.60          | ~ (v1_relat_1 @ X1))),
% 3.35/3.60      inference('sup-', [status(thm)], ['1', '3'])).
% 3.35/3.60  thf('5', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.35/3.60         (~ (v1_relat_1 @ X0)
% 3.35/3.60          | ~ (v1_relat_1 @ X1)
% 3.35/3.60          | ~ (v1_relat_1 @ X1)
% 3.35/3.60          | (r2_hidden @ 
% 3.35/3.60             (k4_tarski @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 3.35/3.60              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 3.35/3.60               (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 3.35/3.60             X1)
% 3.35/3.60          | ~ (v1_relat_1 @ X0)
% 3.35/3.60          | ((X2) = (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 3.35/3.60          | (r2_hidden @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X2))),
% 3.35/3.60      inference('sup-', [status(thm)], ['0', '4'])).
% 3.35/3.60  thf('6', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.35/3.60         ((r2_hidden @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X2)
% 3.35/3.60          | ((X2) = (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 3.35/3.60          | (r2_hidden @ 
% 3.35/3.60             (k4_tarski @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 3.35/3.60              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 3.35/3.60               (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 3.35/3.60             X1)
% 3.35/3.60          | ~ (v1_relat_1 @ X1)
% 3.35/3.60          | ~ (v1_relat_1 @ X0))),
% 3.35/3.60      inference('simplify', [status(thm)], ['5'])).
% 3.35/3.60  thf('7', plain,
% 3.35/3.60      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 3.35/3.60         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6)
% 3.35/3.60          | (r2_hidden @ X4 @ X7)
% 3.35/3.60          | ((X7) != (k1_relat_1 @ X6)))),
% 3.35/3.60      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.35/3.60  thf('8', plain,
% 3.35/3.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.35/3.60         ((r2_hidden @ X4 @ (k1_relat_1 @ X6))
% 3.35/3.60          | ~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6))),
% 3.35/3.60      inference('simplify', [status(thm)], ['7'])).
% 3.35/3.60  thf('9', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.35/3.60         (~ (v1_relat_1 @ X1)
% 3.35/3.60          | ~ (v1_relat_1 @ X0)
% 3.35/3.60          | ((X2) = (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 3.35/3.60          | (r2_hidden @ (sk_C_1 @ X2 @ (k5_relat_1 @ X0 @ X1)) @ X2)
% 3.35/3.60          | (r2_hidden @ (sk_C_1 @ X2 @ (k5_relat_1 @ X0 @ X1)) @ 
% 3.35/3.60             (k1_relat_1 @ X0)))),
% 3.35/3.60      inference('sup-', [status(thm)], ['6', '8'])).
% 3.35/3.60  thf('10', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i]:
% 3.35/3.60         ((r2_hidden @ (sk_C_1 @ (k1_relat_1 @ X0) @ (k5_relat_1 @ X0 @ X1)) @ 
% 3.35/3.60           (k1_relat_1 @ X0))
% 3.35/3.60          | ((k1_relat_1 @ X0) = (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 3.35/3.60          | ~ (v1_relat_1 @ X0)
% 3.35/3.60          | ~ (v1_relat_1 @ X1))),
% 3.35/3.60      inference('eq_fact', [status(thm)], ['9'])).
% 3.35/3.60  thf('11', plain,
% 3.35/3.60      (![X6 : $i, X9 : $i]:
% 3.35/3.60         (((X9) = (k1_relat_1 @ X6))
% 3.35/3.60          | (r2_hidden @ (k4_tarski @ (sk_C_1 @ X9 @ X6) @ (sk_D @ X9 @ X6)) @ 
% 3.35/3.60             X6)
% 3.35/3.60          | (r2_hidden @ (sk_C_1 @ X9 @ X6) @ X9))),
% 3.35/3.60      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.35/3.60  thf('12', plain,
% 3.35/3.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.35/3.60         ((r2_hidden @ X4 @ (k1_relat_1 @ X6))
% 3.35/3.60          | ~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6))),
% 3.35/3.60      inference('simplify', [status(thm)], ['7'])).
% 3.35/3.60  thf('13', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i]:
% 3.35/3.60         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 3.35/3.60          | ((X1) = (k1_relat_1 @ X0))
% 3.35/3.60          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 3.35/3.60      inference('sup-', [status(thm)], ['11', '12'])).
% 3.35/3.60  thf(d3_tarski, axiom,
% 3.35/3.60    (![A:$i,B:$i]:
% 3.35/3.60     ( ( r1_tarski @ A @ B ) <=>
% 3.35/3.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.35/3.60  thf('14', plain,
% 3.35/3.60      (![X1 : $i, X3 : $i]:
% 3.35/3.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.35/3.60      inference('cnf', [status(esa)], [d3_tarski])).
% 3.35/3.60  thf('15', plain,
% 3.35/3.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.35/3.60         (~ (r2_hidden @ X8 @ X7)
% 3.35/3.60          | (r2_hidden @ (k4_tarski @ X8 @ (sk_D_1 @ X8 @ X6)) @ X6)
% 3.35/3.60          | ((X7) != (k1_relat_1 @ X6)))),
% 3.35/3.60      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.35/3.60  thf('16', plain,
% 3.35/3.60      (![X6 : $i, X8 : $i]:
% 3.35/3.60         ((r2_hidden @ (k4_tarski @ X8 @ (sk_D_1 @ X8 @ X6)) @ X6)
% 3.35/3.60          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X6)))),
% 3.35/3.60      inference('simplify', [status(thm)], ['15'])).
% 3.35/3.60  thf('17', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i]:
% 3.35/3.60         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 3.35/3.60          | (r2_hidden @ 
% 3.35/3.60             (k4_tarski @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 3.35/3.60              (sk_D_1 @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 3.35/3.60             X0))),
% 3.35/3.60      inference('sup-', [status(thm)], ['14', '16'])).
% 3.35/3.60  thf('18', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i]:
% 3.35/3.60         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 3.35/3.60          | (r2_hidden @ 
% 3.35/3.60             (k4_tarski @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 3.35/3.60              (sk_D_1 @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 3.35/3.60             X0))),
% 3.35/3.60      inference('sup-', [status(thm)], ['14', '16'])).
% 3.35/3.60  thf(d5_relat_1, axiom,
% 3.35/3.60    (![A:$i,B:$i]:
% 3.35/3.60     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 3.35/3.60       ( ![C:$i]:
% 3.35/3.60         ( ( r2_hidden @ C @ B ) <=>
% 3.35/3.60           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 3.35/3.60  thf('19', plain,
% 3.35/3.60      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 3.35/3.60         (~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X13)
% 3.35/3.60          | (r2_hidden @ X12 @ X14)
% 3.35/3.60          | ((X14) != (k2_relat_1 @ X13)))),
% 3.35/3.60      inference('cnf', [status(esa)], [d5_relat_1])).
% 3.35/3.60  thf('20', plain,
% 3.35/3.60      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.35/3.60         ((r2_hidden @ X12 @ (k2_relat_1 @ X13))
% 3.35/3.60          | ~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X13))),
% 3.35/3.60      inference('simplify', [status(thm)], ['19'])).
% 3.35/3.60  thf('21', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i]:
% 3.35/3.60         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 3.35/3.60          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X0) @ 
% 3.35/3.60             (k2_relat_1 @ X0)))),
% 3.35/3.60      inference('sup-', [status(thm)], ['18', '20'])).
% 3.35/3.60  thf(t46_relat_1, conjecture,
% 3.35/3.60    (![A:$i]:
% 3.35/3.60     ( ( v1_relat_1 @ A ) =>
% 3.35/3.60       ( ![B:$i]:
% 3.35/3.60         ( ( v1_relat_1 @ B ) =>
% 3.35/3.60           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 3.35/3.60             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 3.35/3.60  thf(zf_stmt_0, negated_conjecture,
% 3.35/3.60    (~( ![A:$i]:
% 3.35/3.60        ( ( v1_relat_1 @ A ) =>
% 3.35/3.60          ( ![B:$i]:
% 3.35/3.60            ( ( v1_relat_1 @ B ) =>
% 3.35/3.60              ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 3.35/3.60                ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ) )),
% 3.35/3.60    inference('cnf.neg', [status(esa)], [t46_relat_1])).
% 3.35/3.60  thf('22', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 3.35/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.60  thf('23', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.35/3.60         (~ (r2_hidden @ X0 @ X1)
% 3.35/3.60          | (r2_hidden @ X0 @ X2)
% 3.35/3.60          | ~ (r1_tarski @ X1 @ X2))),
% 3.35/3.60      inference('cnf', [status(esa)], [d3_tarski])).
% 3.35/3.60  thf('24', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 3.35/3.60          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_A)))),
% 3.35/3.60      inference('sup-', [status(thm)], ['22', '23'])).
% 3.35/3.60  thf('25', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 3.35/3.60          | (r2_hidden @ (sk_D_1 @ (sk_C @ X0 @ (k1_relat_1 @ sk_A)) @ sk_A) @ 
% 3.35/3.60             (k1_relat_1 @ sk_B)))),
% 3.35/3.60      inference('sup-', [status(thm)], ['21', '24'])).
% 3.35/3.60  thf('26', plain,
% 3.35/3.60      (![X6 : $i, X8 : $i]:
% 3.35/3.60         ((r2_hidden @ (k4_tarski @ X8 @ (sk_D_1 @ X8 @ X6)) @ X6)
% 3.35/3.60          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X6)))),
% 3.35/3.60      inference('simplify', [status(thm)], ['15'])).
% 3.35/3.60  thf('27', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 3.35/3.60          | (r2_hidden @ 
% 3.35/3.60             (k4_tarski @ 
% 3.35/3.60              (sk_D_1 @ (sk_C @ X0 @ (k1_relat_1 @ sk_A)) @ sk_A) @ 
% 3.35/3.60              (sk_D_1 @ (sk_D_1 @ (sk_C @ X0 @ (k1_relat_1 @ sk_A)) @ sk_A) @ 
% 3.35/3.60               sk_B)) @ 
% 3.35/3.60             sk_B))),
% 3.35/3.60      inference('sup-', [status(thm)], ['25', '26'])).
% 3.35/3.60  thf('28', plain,
% 3.35/3.60      (![X26 : $i, X27 : $i]:
% 3.35/3.60         (~ (v1_relat_1 @ X26)
% 3.35/3.60          | ~ (v1_relat_1 @ X27)
% 3.35/3.60          | (v1_relat_1 @ (k5_relat_1 @ X26 @ X27)))),
% 3.35/3.60      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 3.35/3.60  thf('29', plain,
% 3.35/3.60      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 3.35/3.60         (~ (v1_relat_1 @ X18)
% 3.35/3.60          | ((X20) != (k5_relat_1 @ X19 @ X18))
% 3.35/3.60          | (r2_hidden @ (k4_tarski @ X21 @ X22) @ X20)
% 3.35/3.60          | ~ (r2_hidden @ (k4_tarski @ X21 @ X23) @ X19)
% 3.35/3.60          | ~ (r2_hidden @ (k4_tarski @ X23 @ X22) @ X18)
% 3.35/3.60          | ~ (v1_relat_1 @ X20)
% 3.35/3.60          | ~ (v1_relat_1 @ X19))),
% 3.35/3.60      inference('cnf', [status(esa)], [d8_relat_1])).
% 3.35/3.60  thf('30', plain,
% 3.35/3.60      (![X18 : $i, X19 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 3.35/3.60         (~ (v1_relat_1 @ X19)
% 3.35/3.60          | ~ (v1_relat_1 @ (k5_relat_1 @ X19 @ X18))
% 3.35/3.60          | ~ (r2_hidden @ (k4_tarski @ X23 @ X22) @ X18)
% 3.35/3.60          | ~ (r2_hidden @ (k4_tarski @ X21 @ X23) @ X19)
% 3.35/3.60          | (r2_hidden @ (k4_tarski @ X21 @ X22) @ (k5_relat_1 @ X19 @ X18))
% 3.35/3.60          | ~ (v1_relat_1 @ X18))),
% 3.35/3.60      inference('simplify', [status(thm)], ['29'])).
% 3.35/3.60  thf('31', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.35/3.60         (~ (v1_relat_1 @ X0)
% 3.35/3.60          | ~ (v1_relat_1 @ X1)
% 3.35/3.60          | ~ (v1_relat_1 @ X0)
% 3.35/3.60          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 3.35/3.60          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 3.35/3.60          | ~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 3.35/3.60          | ~ (v1_relat_1 @ X1))),
% 3.35/3.60      inference('sup-', [status(thm)], ['28', '30'])).
% 3.35/3.60  thf('32', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.35/3.60         (~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 3.35/3.60          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 3.35/3.60          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 3.35/3.60          | ~ (v1_relat_1 @ X1)
% 3.35/3.60          | ~ (v1_relat_1 @ X0))),
% 3.35/3.60      inference('simplify', [status(thm)], ['31'])).
% 3.35/3.60  thf('33', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.35/3.60         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 3.35/3.60          | ~ (v1_relat_1 @ sk_B)
% 3.35/3.60          | ~ (v1_relat_1 @ X1)
% 3.35/3.60          | (r2_hidden @ 
% 3.35/3.60             (k4_tarski @ X2 @ 
% 3.35/3.60              (sk_D_1 @ (sk_D_1 @ (sk_C @ X0 @ (k1_relat_1 @ sk_A)) @ sk_A) @ 
% 3.35/3.60               sk_B)) @ 
% 3.35/3.60             (k5_relat_1 @ X1 @ sk_B))
% 3.35/3.60          | ~ (r2_hidden @ 
% 3.35/3.60               (k4_tarski @ X2 @ 
% 3.35/3.60                (sk_D_1 @ (sk_C @ X0 @ (k1_relat_1 @ sk_A)) @ sk_A)) @ 
% 3.35/3.60               X1))),
% 3.35/3.60      inference('sup-', [status(thm)], ['27', '32'])).
% 3.35/3.60  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 3.35/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.60  thf('35', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.35/3.60         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 3.35/3.60          | ~ (v1_relat_1 @ X1)
% 3.35/3.60          | (r2_hidden @ 
% 3.35/3.60             (k4_tarski @ X2 @ 
% 3.35/3.60              (sk_D_1 @ (sk_D_1 @ (sk_C @ X0 @ (k1_relat_1 @ sk_A)) @ sk_A) @ 
% 3.35/3.60               sk_B)) @ 
% 3.35/3.60             (k5_relat_1 @ X1 @ sk_B))
% 3.35/3.60          | ~ (r2_hidden @ 
% 3.35/3.60               (k4_tarski @ X2 @ 
% 3.35/3.60                (sk_D_1 @ (sk_C @ X0 @ (k1_relat_1 @ sk_A)) @ sk_A)) @ 
% 3.35/3.60               X1))),
% 3.35/3.60      inference('demod', [status(thm)], ['33', '34'])).
% 3.35/3.60  thf('36', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 3.35/3.60          | (r2_hidden @ 
% 3.35/3.60             (k4_tarski @ (sk_C @ X0 @ (k1_relat_1 @ sk_A)) @ 
% 3.35/3.60              (sk_D_1 @ (sk_D_1 @ (sk_C @ X0 @ (k1_relat_1 @ sk_A)) @ sk_A) @ 
% 3.35/3.60               sk_B)) @ 
% 3.35/3.60             (k5_relat_1 @ sk_A @ sk_B))
% 3.35/3.60          | ~ (v1_relat_1 @ sk_A)
% 3.35/3.60          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 3.35/3.60      inference('sup-', [status(thm)], ['17', '35'])).
% 3.35/3.60  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 3.35/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.60  thf('38', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 3.35/3.60          | (r2_hidden @ 
% 3.35/3.60             (k4_tarski @ (sk_C @ X0 @ (k1_relat_1 @ sk_A)) @ 
% 3.35/3.60              (sk_D_1 @ (sk_D_1 @ (sk_C @ X0 @ (k1_relat_1 @ sk_A)) @ sk_A) @ 
% 3.35/3.60               sk_B)) @ 
% 3.35/3.60             (k5_relat_1 @ sk_A @ sk_B))
% 3.35/3.60          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 3.35/3.60      inference('demod', [status(thm)], ['36', '37'])).
% 3.35/3.60  thf('39', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         ((r2_hidden @ 
% 3.35/3.60           (k4_tarski @ (sk_C @ X0 @ (k1_relat_1 @ sk_A)) @ 
% 3.35/3.60            (sk_D_1 @ (sk_D_1 @ (sk_C @ X0 @ (k1_relat_1 @ sk_A)) @ sk_A) @ 
% 3.35/3.60             sk_B)) @ 
% 3.35/3.60           (k5_relat_1 @ sk_A @ sk_B))
% 3.35/3.60          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 3.35/3.60      inference('simplify', [status(thm)], ['38'])).
% 3.35/3.60  thf('40', plain,
% 3.35/3.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.35/3.60         ((r2_hidden @ X4 @ (k1_relat_1 @ X6))
% 3.35/3.60          | ~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6))),
% 3.35/3.60      inference('simplify', [status(thm)], ['7'])).
% 3.35/3.60  thf('41', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 3.35/3.60          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_A)) @ 
% 3.35/3.60             (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 3.35/3.60      inference('sup-', [status(thm)], ['39', '40'])).
% 3.35/3.60  thf('42', plain,
% 3.35/3.60      (![X1 : $i, X3 : $i]:
% 3.35/3.60         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.35/3.60      inference('cnf', [status(esa)], [d3_tarski])).
% 3.35/3.60  thf('43', plain,
% 3.35/3.60      (((r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 3.35/3.60         (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 3.35/3.60        | (r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 3.35/3.60           (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 3.35/3.60      inference('sup-', [status(thm)], ['41', '42'])).
% 3.35/3.60  thf('44', plain,
% 3.35/3.60      ((r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 3.35/3.60        (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 3.35/3.60      inference('simplify', [status(thm)], ['43'])).
% 3.35/3.60  thf('45', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.35/3.60         (~ (r2_hidden @ X0 @ X1)
% 3.35/3.60          | (r2_hidden @ X0 @ X2)
% 3.35/3.60          | ~ (r1_tarski @ X1 @ X2))),
% 3.35/3.60      inference('cnf', [status(esa)], [d3_tarski])).
% 3.35/3.60  thf('46', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         ((r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 3.35/3.60          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_A)))),
% 3.35/3.60      inference('sup-', [status(thm)], ['44', '45'])).
% 3.35/3.60  thf('47', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         ((r2_hidden @ (sk_C_1 @ (k1_relat_1 @ sk_A) @ X0) @ (k1_relat_1 @ X0))
% 3.35/3.60          | ((k1_relat_1 @ sk_A) = (k1_relat_1 @ X0))
% 3.35/3.60          | (r2_hidden @ (sk_C_1 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 3.35/3.60             (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 3.35/3.60      inference('sup-', [status(thm)], ['13', '46'])).
% 3.35/3.60  thf('48', plain,
% 3.35/3.60      ((((k1_relat_1 @ sk_A) = (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 3.35/3.60        | (r2_hidden @ 
% 3.35/3.60           (sk_C_1 @ (k1_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B)) @ 
% 3.35/3.60           (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 3.35/3.60      inference('eq_fact', [status(thm)], ['47'])).
% 3.35/3.60  thf('49', plain,
% 3.35/3.60      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) != (k1_relat_1 @ sk_A))),
% 3.35/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.60  thf('50', plain,
% 3.35/3.60      ((r2_hidden @ 
% 3.35/3.60        (sk_C_1 @ (k1_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B)) @ 
% 3.35/3.60        (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 3.35/3.60      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 3.35/3.60  thf('51', plain,
% 3.35/3.60      (![X6 : $i, X8 : $i]:
% 3.35/3.60         ((r2_hidden @ (k4_tarski @ X8 @ (sk_D_1 @ X8 @ X6)) @ X6)
% 3.35/3.60          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X6)))),
% 3.35/3.60      inference('simplify', [status(thm)], ['15'])).
% 3.35/3.60  thf('52', plain,
% 3.35/3.60      ((r2_hidden @ 
% 3.35/3.60        (k4_tarski @ 
% 3.35/3.60         (sk_C_1 @ (k1_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B)) @ 
% 3.35/3.60         (sk_D_1 @ 
% 3.35/3.60          (sk_C_1 @ (k1_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B)) @ 
% 3.35/3.60          (k5_relat_1 @ sk_A @ sk_B))) @ 
% 3.35/3.60        (k5_relat_1 @ sk_A @ sk_B))),
% 3.35/3.60      inference('sup-', [status(thm)], ['50', '51'])).
% 3.35/3.60  thf('53', plain,
% 3.35/3.60      (![X6 : $i, X9 : $i, X10 : $i]:
% 3.35/3.60         (((X9) = (k1_relat_1 @ X6))
% 3.35/3.60          | ~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X9 @ X6) @ X10) @ X6)
% 3.35/3.60          | ~ (r2_hidden @ (sk_C_1 @ X9 @ X6) @ X9))),
% 3.35/3.60      inference('cnf', [status(esa)], [d4_relat_1])).
% 3.35/3.60  thf('54', plain,
% 3.35/3.60      ((~ (r2_hidden @ 
% 3.35/3.60           (sk_C_1 @ (k1_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B)) @ 
% 3.35/3.60           (k1_relat_1 @ sk_A))
% 3.35/3.60        | ((k1_relat_1 @ sk_A) = (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 3.35/3.60      inference('sup-', [status(thm)], ['52', '53'])).
% 3.35/3.60  thf('55', plain,
% 3.35/3.60      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) != (k1_relat_1 @ sk_A))),
% 3.35/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.60  thf('56', plain,
% 3.35/3.60      (~ (r2_hidden @ 
% 3.35/3.60          (sk_C_1 @ (k1_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B)) @ 
% 3.35/3.60          (k1_relat_1 @ sk_A))),
% 3.35/3.60      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 3.35/3.60  thf('57', plain,
% 3.35/3.60      ((~ (v1_relat_1 @ sk_B)
% 3.35/3.60        | ~ (v1_relat_1 @ sk_A)
% 3.35/3.60        | ((k1_relat_1 @ sk_A) = (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 3.35/3.60      inference('sup-', [status(thm)], ['10', '56'])).
% 3.35/3.60  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 3.35/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.60  thf('59', plain, ((v1_relat_1 @ sk_A)),
% 3.35/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.60  thf('60', plain,
% 3.35/3.60      (((k1_relat_1 @ sk_A) = (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 3.35/3.60      inference('demod', [status(thm)], ['57', '58', '59'])).
% 3.35/3.60  thf('61', plain,
% 3.35/3.60      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) != (k1_relat_1 @ sk_A))),
% 3.35/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.60  thf('62', plain, ($false),
% 3.35/3.60      inference('simplify_reflect-', [status(thm)], ['60', '61'])).
% 3.35/3.60  
% 3.35/3.60  % SZS output end Refutation
% 3.35/3.60  
% 3.35/3.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

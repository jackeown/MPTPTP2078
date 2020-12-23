%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0459+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ShFE9NFWZ2

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:57 EST 2020

% Result     : Theorem 4.25s
% Output     : Refutation 4.25s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 119 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :   22
%              Number of atoms          : 1021 (1508 expanded)
%              Number of equality atoms :   27 (  56 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

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

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16
        = ( k2_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X16 @ X13 ) @ ( sk_C_2 @ X16 @ X13 ) ) @ X13 )
      | ( r2_hidden @ ( sk_C_2 @ X16 @ X13 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

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
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X24 @ X21 @ X18 @ X19 ) @ X24 ) @ X18 )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X24 ) @ X20 )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('3',plain,(
    ! [X18: $i,X19: $i,X21: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X18 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X24 ) @ ( k5_relat_1 @ X19 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X24 @ X21 @ X18 @ X19 ) @ X24 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_2 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D_2 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_2 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_2 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D_2 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_2 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C_2 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_D_2 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C_2 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X13 )
      | ( r2_hidden @ X12 @ X14 )
      | ( X14
       != ( k2_relat_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ ( k2_relat_1 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X13 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X2
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C_2 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ ( k2_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['9'])).

thf('11',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16
        = ( k2_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X16 @ X13 ) @ ( sk_C_2 @ X16 @ X13 ) ) @ X13 )
      | ( r2_hidden @ ( sk_C_2 @ X16 @ X13 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ ( k2_relat_1 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X13 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X15 @ X13 ) @ X15 ) @ X13 )
      | ( X14
       != ( k2_relat_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('16',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X15 @ X13 ) @ X15 ) @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_3 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf(t47_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
             => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
                = ( k2_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_relat_1])).

thf('21',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D_3 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X15 @ X13 ) @ X15 ) @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_D_3 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ sk_B ) @ ( sk_D_3 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

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
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_D_3 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_D_3 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ sk_B ) @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) ) ) @ ( k5_relat_1 @ sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_D_3 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ sk_B ) @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) ) ) @ ( k5_relat_1 @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_D_3 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ sk_B ) @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) ) ) @ ( k5_relat_1 @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ ( k2_relat_1 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X13 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_A ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ ( k2_relat_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ sk_A )
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ ( k2_relat_1 @ sk_A ) @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','45'])).

thf('47',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ ( sk_C_2 @ ( k2_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ sk_A ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(eq_fact,[status(thm)],['46'])).

thf('48',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r2_hidden @ ( sk_C_2 @ ( k2_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ sk_A ) ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X15 @ X13 ) @ X15 ) @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('51',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_C_2 @ ( k2_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ sk_A ) ) @ ( k5_relat_1 @ sk_B @ sk_A ) ) @ ( sk_C_2 @ ( k2_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) @ ( k5_relat_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X13: $i,X16: $i,X17: $i] :
      ( ( X16
        = ( k2_relat_1 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_C_2 @ X16 @ X13 ) ) @ X13 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X16 @ X13 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('53',plain,
    ( ~ ( r2_hidden @ ( sk_C_2 @ ( k2_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_A )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ~ ( r2_hidden @ ( sk_C_2 @ ( k2_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k2_relat_1 @ sk_A )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).


%------------------------------------------------------------------------------

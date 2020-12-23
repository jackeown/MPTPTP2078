%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3BNVJDV5AZ

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:57 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 131 expanded)
%              Number of leaves         :   17 (  42 expanded)
%              Depth                    :   22
%              Number of atoms          : 1193 (1943 expanded)
%              Number of equality atoms :   14 (  24 expanded)
%              Maximal formula depth    :   20 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X18 @ X19 ) ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X5 @ X6 ) @ ( sk_D_1 @ X5 @ X6 ) ) @ X6 )
      | ( r1_tarski @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( X12
       != ( k5_relat_1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X16 @ X13 @ X10 @ X11 ) @ X16 ) @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X16 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('4',plain,(
    ! [X10: $i,X11: $i,X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X16 ) @ ( k5_relat_1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X16 @ X13 @ X10 @ X11 ) @ X16 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
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
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(d10_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ! [C: $i,D: $i] :
            ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
          <=> ( ( r2_hidden @ C @ A )
              & ( C = D ) ) ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k6_relat_1 @ X1 ) )
      | ( X2 = X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k6_relat_1 @ X1 ) )
      | ( X2 = X3 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('11',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k6_relat_1 @ X1 ) )
      | ( X2 = X3 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( ( sk_F_1 @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( ( sk_F_1 @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X5 @ X6 ) @ ( sk_D_1 @ X5 @ X6 ) ) @ X6 )
      | ( r1_tarski @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( X12
       != ( k5_relat_1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_F_1 @ X16 @ X13 @ X10 @ X11 ) ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X16 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X16 ) @ ( k5_relat_1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_F_1 @ X16 @ X13 @ X10 @ X11 ) ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['15','23'])).

thf('25',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X5 @ X6 ) @ ( sk_D_1 @ X5 @ X6 ) ) @ X5 )
      | ( r1_tarski @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','30'])).

thf('32',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t76_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
          & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_relat_1])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B )
    | ~ ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B )
   <= ~ ( r1_tarski @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('39',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k6_relat_1 @ X1 ) )
      | ( X2 = X3 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 )
      | ( ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( sk_F_1 @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 )
      | ( ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( sk_F_1 @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X5 @ X6 ) @ ( sk_D_1 @ X5 @ X6 ) ) @ X5 )
      | ( r1_tarski @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','50'])).

thf('52',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ~ ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['35'])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ sk_B )
   <= ~ ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( r1_tarski @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B )
    | ~ ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['35'])).

thf('60',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['36','60'])).

thf('62',plain,(
    ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['62','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3BNVJDV5AZ
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:31:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.51/1.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.51/1.68  % Solved by: fo/fo7.sh
% 1.51/1.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.51/1.68  % done 2583 iterations in 1.185s
% 1.51/1.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.51/1.68  % SZS output start Refutation
% 1.51/1.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.51/1.68  thf(sk_B_type, type, sk_B: $i).
% 1.51/1.68  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.51/1.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.51/1.68  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.51/1.68  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.51/1.68  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 1.51/1.68  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 1.51/1.68  thf(sk_A_type, type, sk_A: $i).
% 1.51/1.68  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.51/1.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.51/1.68  thf(dt_k5_relat_1, axiom,
% 1.51/1.68    (![A:$i,B:$i]:
% 1.51/1.68     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 1.51/1.68       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 1.51/1.68  thf('0', plain,
% 1.51/1.68      (![X18 : $i, X19 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ X18)
% 1.51/1.68          | ~ (v1_relat_1 @ X19)
% 1.51/1.68          | (v1_relat_1 @ (k5_relat_1 @ X18 @ X19)))),
% 1.51/1.68      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.51/1.68  thf('1', plain,
% 1.51/1.68      (![X18 : $i, X19 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ X18)
% 1.51/1.68          | ~ (v1_relat_1 @ X19)
% 1.51/1.68          | (v1_relat_1 @ (k5_relat_1 @ X18 @ X19)))),
% 1.51/1.68      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.51/1.68  thf(d3_relat_1, axiom,
% 1.51/1.68    (![A:$i]:
% 1.51/1.68     ( ( v1_relat_1 @ A ) =>
% 1.51/1.68       ( ![B:$i]:
% 1.51/1.68         ( ( r1_tarski @ A @ B ) <=>
% 1.51/1.68           ( ![C:$i,D:$i]:
% 1.51/1.68             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 1.51/1.68               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 1.51/1.68  thf('2', plain,
% 1.51/1.68      (![X5 : $i, X6 : $i]:
% 1.51/1.68         ((r2_hidden @ (k4_tarski @ (sk_C_1 @ X5 @ X6) @ (sk_D_1 @ X5 @ X6)) @ 
% 1.51/1.68           X6)
% 1.51/1.68          | (r1_tarski @ X6 @ X5)
% 1.51/1.68          | ~ (v1_relat_1 @ X6))),
% 1.51/1.68      inference('cnf', [status(esa)], [d3_relat_1])).
% 1.51/1.68  thf(d8_relat_1, axiom,
% 1.51/1.68    (![A:$i]:
% 1.51/1.68     ( ( v1_relat_1 @ A ) =>
% 1.51/1.68       ( ![B:$i]:
% 1.51/1.68         ( ( v1_relat_1 @ B ) =>
% 1.51/1.68           ( ![C:$i]:
% 1.51/1.68             ( ( v1_relat_1 @ C ) =>
% 1.51/1.68               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 1.51/1.68                 ( ![D:$i,E:$i]:
% 1.51/1.68                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 1.51/1.68                     ( ?[F:$i]:
% 1.51/1.68                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 1.51/1.68                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 1.51/1.68  thf('3', plain,
% 1.51/1.68      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X16 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ X10)
% 1.51/1.68          | ((X12) != (k5_relat_1 @ X11 @ X10))
% 1.51/1.68          | (r2_hidden @ 
% 1.51/1.68             (k4_tarski @ (sk_F_1 @ X16 @ X13 @ X10 @ X11) @ X16) @ X10)
% 1.51/1.68          | ~ (r2_hidden @ (k4_tarski @ X13 @ X16) @ X12)
% 1.51/1.68          | ~ (v1_relat_1 @ X12)
% 1.51/1.68          | ~ (v1_relat_1 @ X11))),
% 1.51/1.68      inference('cnf', [status(esa)], [d8_relat_1])).
% 1.51/1.68  thf('4', plain,
% 1.51/1.68      (![X10 : $i, X11 : $i, X13 : $i, X16 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ X11)
% 1.51/1.68          | ~ (v1_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 1.51/1.68          | ~ (r2_hidden @ (k4_tarski @ X13 @ X16) @ (k5_relat_1 @ X11 @ X10))
% 1.51/1.68          | (r2_hidden @ 
% 1.51/1.68             (k4_tarski @ (sk_F_1 @ X16 @ X13 @ X10 @ X11) @ X16) @ X10)
% 1.51/1.68          | ~ (v1_relat_1 @ X10))),
% 1.51/1.68      inference('simplify', [status(thm)], ['3'])).
% 1.51/1.68  thf('5', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 1.51/1.68          | ~ (v1_relat_1 @ X0)
% 1.51/1.68          | (r2_hidden @ 
% 1.51/1.68             (k4_tarski @ 
% 1.51/1.68              (sk_F_1 @ (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.51/1.68               (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 1.51/1.68              (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 1.51/1.68             X0)
% 1.51/1.68          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.51/1.68          | ~ (v1_relat_1 @ X1))),
% 1.51/1.68      inference('sup-', [status(thm)], ['2', '4'])).
% 1.51/1.68  thf('6', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ X1)
% 1.51/1.68          | (r2_hidden @ 
% 1.51/1.68             (k4_tarski @ 
% 1.51/1.68              (sk_F_1 @ (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.51/1.68               (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 1.51/1.68              (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 1.51/1.68             X0)
% 1.51/1.68          | ~ (v1_relat_1 @ X0)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 1.51/1.68          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 1.51/1.68      inference('simplify', [status(thm)], ['5'])).
% 1.51/1.68  thf('7', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ X0)
% 1.51/1.68          | ~ (v1_relat_1 @ X1)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 1.51/1.68          | ~ (v1_relat_1 @ X0)
% 1.51/1.68          | (r2_hidden @ 
% 1.51/1.68             (k4_tarski @ 
% 1.51/1.68              (sk_F_1 @ (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.51/1.68               (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 1.51/1.68              (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 1.51/1.68             X0)
% 1.51/1.68          | ~ (v1_relat_1 @ X1))),
% 1.51/1.68      inference('sup-', [status(thm)], ['1', '6'])).
% 1.51/1.68  thf('8', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.68         ((r2_hidden @ 
% 1.51/1.68           (k4_tarski @ 
% 1.51/1.68            (sk_F_1 @ (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.51/1.68             (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 1.51/1.68            (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 1.51/1.68           X0)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 1.51/1.68          | ~ (v1_relat_1 @ X1)
% 1.51/1.68          | ~ (v1_relat_1 @ X0))),
% 1.51/1.68      inference('simplify', [status(thm)], ['7'])).
% 1.51/1.68  thf(d10_relat_1, axiom,
% 1.51/1.68    (![A:$i,B:$i]:
% 1.51/1.68     ( ( v1_relat_1 @ B ) =>
% 1.51/1.68       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 1.51/1.68         ( ![C:$i,D:$i]:
% 1.51/1.68           ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 1.51/1.68             ( ( r2_hidden @ C @ A ) & ( ( C ) = ( D ) ) ) ) ) ) ))).
% 1.51/1.68  thf('9', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.51/1.68         (((X0) != (k6_relat_1 @ X1))
% 1.51/1.68          | ((X2) = (X3))
% 1.51/1.68          | ~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ X0)
% 1.51/1.68          | ~ (v1_relat_1 @ X0))),
% 1.51/1.68      inference('cnf', [status(esa)], [d10_relat_1])).
% 1.51/1.68  thf('10', plain,
% 1.51/1.68      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.51/1.68          | ~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k6_relat_1 @ X1))
% 1.51/1.68          | ((X2) = (X3)))),
% 1.51/1.68      inference('simplify', [status(thm)], ['9'])).
% 1.51/1.68  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 1.51/1.68  thf('11', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 1.51/1.68      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.51/1.68  thf('12', plain,
% 1.51/1.68      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.51/1.68         (~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k6_relat_1 @ X1))
% 1.51/1.68          | ((X2) = (X3)))),
% 1.51/1.68      inference('demod', [status(thm)], ['10', '11'])).
% 1.51/1.68  thf('13', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.51/1.68          | ~ (v1_relat_1 @ X1)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 1.51/1.68          | ((sk_F_1 @ (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 1.51/1.68              (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 1.51/1.68              (k6_relat_1 @ X0) @ X1)
% 1.51/1.68              = (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))))),
% 1.51/1.68      inference('sup-', [status(thm)], ['8', '12'])).
% 1.51/1.68  thf('14', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 1.51/1.68      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.51/1.68  thf('15', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ X1)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 1.51/1.68          | ((sk_F_1 @ (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 1.51/1.68              (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 1.51/1.68              (k6_relat_1 @ X0) @ X1)
% 1.51/1.68              = (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))))),
% 1.51/1.68      inference('demod', [status(thm)], ['13', '14'])).
% 1.51/1.68  thf('16', plain,
% 1.51/1.68      (![X18 : $i, X19 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ X18)
% 1.51/1.68          | ~ (v1_relat_1 @ X19)
% 1.51/1.68          | (v1_relat_1 @ (k5_relat_1 @ X18 @ X19)))),
% 1.51/1.68      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.51/1.68  thf('17', plain,
% 1.51/1.68      (![X5 : $i, X6 : $i]:
% 1.51/1.68         ((r2_hidden @ (k4_tarski @ (sk_C_1 @ X5 @ X6) @ (sk_D_1 @ X5 @ X6)) @ 
% 1.51/1.68           X6)
% 1.51/1.68          | (r1_tarski @ X6 @ X5)
% 1.51/1.68          | ~ (v1_relat_1 @ X6))),
% 1.51/1.68      inference('cnf', [status(esa)], [d3_relat_1])).
% 1.51/1.68  thf('18', plain,
% 1.51/1.68      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X16 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ X10)
% 1.51/1.68          | ((X12) != (k5_relat_1 @ X11 @ X10))
% 1.51/1.68          | (r2_hidden @ 
% 1.51/1.68             (k4_tarski @ X13 @ (sk_F_1 @ X16 @ X13 @ X10 @ X11)) @ X11)
% 1.51/1.68          | ~ (r2_hidden @ (k4_tarski @ X13 @ X16) @ X12)
% 1.51/1.68          | ~ (v1_relat_1 @ X12)
% 1.51/1.68          | ~ (v1_relat_1 @ X11))),
% 1.51/1.68      inference('cnf', [status(esa)], [d8_relat_1])).
% 1.51/1.68  thf('19', plain,
% 1.51/1.68      (![X10 : $i, X11 : $i, X13 : $i, X16 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ X11)
% 1.51/1.68          | ~ (v1_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 1.51/1.68          | ~ (r2_hidden @ (k4_tarski @ X13 @ X16) @ (k5_relat_1 @ X11 @ X10))
% 1.51/1.68          | (r2_hidden @ 
% 1.51/1.68             (k4_tarski @ X13 @ (sk_F_1 @ X16 @ X13 @ X10 @ X11)) @ X11)
% 1.51/1.68          | ~ (v1_relat_1 @ X10))),
% 1.51/1.68      inference('simplify', [status(thm)], ['18'])).
% 1.51/1.68  thf('20', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 1.51/1.68          | ~ (v1_relat_1 @ X0)
% 1.51/1.68          | (r2_hidden @ 
% 1.51/1.68             (k4_tarski @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.51/1.68              (sk_F_1 @ (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.51/1.68               (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 1.51/1.68             X1)
% 1.51/1.68          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.51/1.68          | ~ (v1_relat_1 @ X1))),
% 1.51/1.68      inference('sup-', [status(thm)], ['17', '19'])).
% 1.51/1.68  thf('21', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ X1)
% 1.51/1.68          | (r2_hidden @ 
% 1.51/1.68             (k4_tarski @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.51/1.68              (sk_F_1 @ (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.51/1.68               (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 1.51/1.68             X1)
% 1.51/1.68          | ~ (v1_relat_1 @ X0)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 1.51/1.68          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 1.51/1.68      inference('simplify', [status(thm)], ['20'])).
% 1.51/1.68  thf('22', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ X0)
% 1.51/1.68          | ~ (v1_relat_1 @ X1)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 1.51/1.68          | ~ (v1_relat_1 @ X0)
% 1.51/1.68          | (r2_hidden @ 
% 1.51/1.68             (k4_tarski @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.51/1.68              (sk_F_1 @ (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.51/1.68               (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 1.51/1.68             X1)
% 1.51/1.68          | ~ (v1_relat_1 @ X1))),
% 1.51/1.68      inference('sup-', [status(thm)], ['16', '21'])).
% 1.51/1.68  thf('23', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.68         ((r2_hidden @ 
% 1.51/1.68           (k4_tarski @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.51/1.68            (sk_F_1 @ (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.51/1.68             (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 1.51/1.68           X1)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 1.51/1.68          | ~ (v1_relat_1 @ X1)
% 1.51/1.68          | ~ (v1_relat_1 @ X0))),
% 1.51/1.68      inference('simplify', [status(thm)], ['22'])).
% 1.51/1.68  thf('24', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.68         ((r2_hidden @ 
% 1.51/1.68           (k4_tarski @ 
% 1.51/1.68            (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 1.51/1.68            (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 1.51/1.68           X1)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 1.51/1.68          | ~ (v1_relat_1 @ X1)
% 1.51/1.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.51/1.68          | ~ (v1_relat_1 @ X1)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2))),
% 1.51/1.68      inference('sup+', [status(thm)], ['15', '23'])).
% 1.51/1.68  thf('25', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 1.51/1.68      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.51/1.68  thf('26', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.68         ((r2_hidden @ 
% 1.51/1.68           (k4_tarski @ 
% 1.51/1.68            (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 1.51/1.68            (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 1.51/1.68           X1)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 1.51/1.68          | ~ (v1_relat_1 @ X1)
% 1.51/1.68          | ~ (v1_relat_1 @ X1)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2))),
% 1.51/1.68      inference('demod', [status(thm)], ['24', '25'])).
% 1.51/1.68  thf('27', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ X1)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 1.51/1.68          | (r2_hidden @ 
% 1.51/1.68             (k4_tarski @ 
% 1.51/1.68              (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 1.51/1.68              (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))) @ 
% 1.51/1.68             X1))),
% 1.51/1.68      inference('simplify', [status(thm)], ['26'])).
% 1.51/1.68  thf('28', plain,
% 1.51/1.68      (![X5 : $i, X6 : $i]:
% 1.51/1.68         (~ (r2_hidden @ 
% 1.51/1.68             (k4_tarski @ (sk_C_1 @ X5 @ X6) @ (sk_D_1 @ X5 @ X6)) @ X5)
% 1.51/1.68          | (r1_tarski @ X6 @ X5)
% 1.51/1.68          | ~ (v1_relat_1 @ X6))),
% 1.51/1.68      inference('cnf', [status(esa)], [d3_relat_1])).
% 1.51/1.68  thf('29', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i]:
% 1.51/1.68         ((r1_tarski @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X0)
% 1.51/1.68          | ~ (v1_relat_1 @ X0)
% 1.51/1.68          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X0))),
% 1.51/1.68      inference('sup-', [status(thm)], ['27', '28'])).
% 1.51/1.68  thf('30', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 1.51/1.68          | ~ (v1_relat_1 @ X0)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X0))),
% 1.51/1.68      inference('simplify', [status(thm)], ['29'])).
% 1.51/1.68  thf('31', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.51/1.68          | ~ (v1_relat_1 @ X1)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X1)
% 1.51/1.68          | ~ (v1_relat_1 @ X1))),
% 1.51/1.68      inference('sup-', [status(thm)], ['0', '30'])).
% 1.51/1.68  thf('32', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 1.51/1.68      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.51/1.68  thf('33', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ X1)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X1)
% 1.51/1.68          | ~ (v1_relat_1 @ X1))),
% 1.51/1.68      inference('demod', [status(thm)], ['31', '32'])).
% 1.51/1.68  thf('34', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i]:
% 1.51/1.68         ((r1_tarski @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X1)
% 1.51/1.68          | ~ (v1_relat_1 @ X1))),
% 1.51/1.68      inference('simplify', [status(thm)], ['33'])).
% 1.51/1.68  thf(t76_relat_1, conjecture,
% 1.51/1.68    (![A:$i,B:$i]:
% 1.51/1.68     ( ( v1_relat_1 @ B ) =>
% 1.51/1.68       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 1.51/1.68         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 1.51/1.68  thf(zf_stmt_0, negated_conjecture,
% 1.51/1.68    (~( ![A:$i,B:$i]:
% 1.51/1.68        ( ( v1_relat_1 @ B ) =>
% 1.51/1.68          ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 1.51/1.68            ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )),
% 1.51/1.68    inference('cnf.neg', [status(esa)], [t76_relat_1])).
% 1.51/1.68  thf('35', plain,
% 1.51/1.68      ((~ (r1_tarski @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) @ sk_B)
% 1.51/1.68        | ~ (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ sk_B))),
% 1.51/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.68  thf('36', plain,
% 1.51/1.68      ((~ (r1_tarski @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) @ sk_B))
% 1.51/1.68         <= (~ ((r1_tarski @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) @ sk_B)))),
% 1.51/1.68      inference('split', [status(esa)], ['35'])).
% 1.51/1.68  thf('37', plain,
% 1.51/1.68      (![X18 : $i, X19 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ X18)
% 1.51/1.68          | ~ (v1_relat_1 @ X19)
% 1.51/1.68          | (v1_relat_1 @ (k5_relat_1 @ X18 @ X19)))),
% 1.51/1.68      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.51/1.68  thf('38', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.68         ((r2_hidden @ 
% 1.51/1.68           (k4_tarski @ (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.51/1.68            (sk_F_1 @ (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.51/1.68             (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 1.51/1.68           X1)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 1.51/1.68          | ~ (v1_relat_1 @ X1)
% 1.51/1.68          | ~ (v1_relat_1 @ X0))),
% 1.51/1.68      inference('simplify', [status(thm)], ['22'])).
% 1.51/1.68  thf('39', plain,
% 1.51/1.68      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.51/1.68         (~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k6_relat_1 @ X1))
% 1.51/1.68          | ((X2) = (X3)))),
% 1.51/1.68      inference('demod', [status(thm)], ['10', '11'])).
% 1.51/1.68  thf('40', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ X1)
% 1.51/1.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X2)
% 1.51/1.68          | ((sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.51/1.68              = (sk_F_1 @ 
% 1.51/1.68                 (sk_D_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ 
% 1.51/1.68                 (sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ X1 @ 
% 1.51/1.68                 (k6_relat_1 @ X0))))),
% 1.51/1.68      inference('sup-', [status(thm)], ['38', '39'])).
% 1.51/1.68  thf('41', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 1.51/1.68      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.51/1.68  thf('42', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ X1)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X2)
% 1.51/1.68          | ((sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.51/1.68              = (sk_F_1 @ 
% 1.51/1.68                 (sk_D_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ 
% 1.51/1.68                 (sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ X1 @ 
% 1.51/1.68                 (k6_relat_1 @ X0))))),
% 1.51/1.68      inference('demod', [status(thm)], ['40', '41'])).
% 1.51/1.68  thf('43', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.68         ((r2_hidden @ 
% 1.51/1.68           (k4_tarski @ 
% 1.51/1.68            (sk_F_1 @ (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.51/1.68             (sk_C_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 1.51/1.68            (sk_D_1 @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 1.51/1.68           X0)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 1.51/1.68          | ~ (v1_relat_1 @ X1)
% 1.51/1.68          | ~ (v1_relat_1 @ X0))),
% 1.51/1.68      inference('simplify', [status(thm)], ['7'])).
% 1.51/1.68  thf('44', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.68         ((r2_hidden @ 
% 1.51/1.68           (k4_tarski @ 
% 1.51/1.68            (sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 1.51/1.68            (sk_D_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 1.51/1.68           X0)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 1.51/1.68          | ~ (v1_relat_1 @ X0)
% 1.51/1.68          | ~ (v1_relat_1 @ X0)
% 1.51/1.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2))),
% 1.51/1.68      inference('sup+', [status(thm)], ['42', '43'])).
% 1.51/1.68  thf('45', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 1.51/1.68      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.51/1.68  thf('46', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.68         ((r2_hidden @ 
% 1.51/1.68           (k4_tarski @ 
% 1.51/1.68            (sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 1.51/1.68            (sk_D_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 1.51/1.68           X0)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 1.51/1.68          | ~ (v1_relat_1 @ X0)
% 1.51/1.68          | ~ (v1_relat_1 @ X0)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2))),
% 1.51/1.68      inference('demod', [status(thm)], ['44', '45'])).
% 1.51/1.68  thf('47', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ X0)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2)
% 1.51/1.68          | (r2_hidden @ 
% 1.51/1.68             (k4_tarski @ 
% 1.51/1.68              (sk_C_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 1.51/1.68              (sk_D_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 1.51/1.68             X0))),
% 1.51/1.68      inference('simplify', [status(thm)], ['46'])).
% 1.51/1.68  thf('48', plain,
% 1.51/1.68      (![X5 : $i, X6 : $i]:
% 1.51/1.68         (~ (r2_hidden @ 
% 1.51/1.68             (k4_tarski @ (sk_C_1 @ X5 @ X6) @ (sk_D_1 @ X5 @ X6)) @ X5)
% 1.51/1.68          | (r1_tarski @ X6 @ X5)
% 1.51/1.68          | ~ (v1_relat_1 @ X6))),
% 1.51/1.68      inference('cnf', [status(esa)], [d3_relat_1])).
% 1.51/1.68  thf('49', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i]:
% 1.51/1.68         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)
% 1.51/1.68          | ~ (v1_relat_1 @ X0)
% 1.51/1.68          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0))),
% 1.51/1.68      inference('sup-', [status(thm)], ['47', '48'])).
% 1.51/1.68  thf('50', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.51/1.68          | ~ (v1_relat_1 @ X0)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0))),
% 1.51/1.68      inference('simplify', [status(thm)], ['49'])).
% 1.51/1.68  thf('51', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ X0)
% 1.51/1.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)
% 1.51/1.68          | ~ (v1_relat_1 @ X0))),
% 1.51/1.68      inference('sup-', [status(thm)], ['37', '50'])).
% 1.51/1.68  thf('52', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 1.51/1.68      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.51/1.68  thf('53', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i]:
% 1.51/1.68         (~ (v1_relat_1 @ X0)
% 1.51/1.68          | (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)
% 1.51/1.68          | ~ (v1_relat_1 @ X0))),
% 1.51/1.68      inference('demod', [status(thm)], ['51', '52'])).
% 1.51/1.68  thf('54', plain,
% 1.51/1.68      (![X0 : $i, X1 : $i]:
% 1.51/1.68         ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)
% 1.51/1.68          | ~ (v1_relat_1 @ X0))),
% 1.51/1.68      inference('simplify', [status(thm)], ['53'])).
% 1.51/1.68  thf('55', plain,
% 1.51/1.68      ((~ (r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ sk_B))
% 1.51/1.68         <= (~ ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ sk_B)))),
% 1.51/1.68      inference('split', [status(esa)], ['35'])).
% 1.51/1.68  thf('56', plain,
% 1.51/1.68      ((~ (v1_relat_1 @ sk_B))
% 1.51/1.68         <= (~ ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ sk_B)))),
% 1.51/1.68      inference('sup-', [status(thm)], ['54', '55'])).
% 1.51/1.68  thf('57', plain, ((v1_relat_1 @ sk_B)),
% 1.51/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.68  thf('58', plain,
% 1.51/1.68      (((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ sk_B))),
% 1.51/1.68      inference('demod', [status(thm)], ['56', '57'])).
% 1.51/1.68  thf('59', plain,
% 1.51/1.68      (~ ((r1_tarski @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) @ sk_B)) | 
% 1.51/1.68       ~ ((r1_tarski @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ sk_B))),
% 1.51/1.68      inference('split', [status(esa)], ['35'])).
% 1.51/1.68  thf('60', plain,
% 1.51/1.68      (~ ((r1_tarski @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) @ sk_B))),
% 1.51/1.68      inference('sat_resolution*', [status(thm)], ['58', '59'])).
% 1.51/1.68  thf('61', plain,
% 1.51/1.68      (~ (r1_tarski @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) @ sk_B)),
% 1.51/1.68      inference('simpl_trail', [status(thm)], ['36', '60'])).
% 1.51/1.68  thf('62', plain, (~ (v1_relat_1 @ sk_B)),
% 1.51/1.68      inference('sup-', [status(thm)], ['34', '61'])).
% 1.51/1.68  thf('63', plain, ((v1_relat_1 @ sk_B)),
% 1.51/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.68  thf('64', plain, ($false), inference('demod', [status(thm)], ['62', '63'])).
% 1.51/1.68  
% 1.51/1.68  % SZS output end Refutation
% 1.51/1.68  
% 1.51/1.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

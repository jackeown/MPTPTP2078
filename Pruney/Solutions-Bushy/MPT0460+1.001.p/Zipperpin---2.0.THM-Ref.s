%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0460+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dozgutaXmj

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:57 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   63 (  83 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :   22
%              Number of atoms          : 1014 (1327 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   21 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X13 @ X14 ) ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( X7
       != ( k5_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_F_1 @ X11 @ X8 @ X5 @ X6 ) ) @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X11 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('4',plain,(
    ! [X5: $i,X6: $i,X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X11 ) @ ( k5_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_F_1 @ X11 @ X8 @ X5 @ X6 ) ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
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
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

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

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( X7
       != ( k5_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X11 @ X8 @ X5 @ X6 ) @ X11 ) @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X11 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('13',plain,(
    ! [X5: $i,X6: $i,X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X11 ) @ ( k5_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X11 @ X8 @ X5 @ X6 ) @ X11 ) @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X3 )
      | ~ ( r1_tarski @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X3 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ ( sk_C @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ sk_A @ X0 ) @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ ( sk_C @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ sk_A @ X0 ) @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('25',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( X7
       != ( k5_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X9 ) @ X5 )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('26',plain,(
    ! [X5: $i,X6: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X9 ) @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ X6 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ ( k5_relat_1 @ X6 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) ) @ ( k5_relat_1 @ X2 @ sk_B ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_F_1 @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ ( sk_C @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ sk_A @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) ) @ ( k5_relat_1 @ X2 @ sk_B ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_F_1 @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ ( sk_C @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ sk_A @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) ) @ ( k5_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) ) @ ( k5_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) @ ( sk_D @ X1 @ ( k5_relat_1 @ X0 @ sk_A ) ) ) @ ( k5_relat_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ ( k5_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ ( k5_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ sk_A ) )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ ( k5_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ ( k5_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ ( k5_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ sk_A ) @ ( k5_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_C_1 @ sk_A ) @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['44','45'])).


%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gGpiQpcVDH

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 (  83 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :   20
%              Number of atoms          : 1016 (1329 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   23 (  10 average)

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

thf(t49_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( r1_tarski @ A @ B )
               => ( r1_tarski @ ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( ( r1_tarski @ A @ B )
                 => ( r1_tarski @ ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_relat_1])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
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

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( X7
       != ( k5_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_F_1 @ X11 @ X8 @ X5 @ X6 ) ) @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X11 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X11 ) @ ( k5_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_F_1 @ X11 @ X8 @ X5 @ X6 ) ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X1 @ X0 ) ) @ X3 )
      | ~ ( r1_tarski @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X1 @ X0 ) ) @ X3 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k5_relat_1 @ sk_A @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k5_relat_1 @ sk_A @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X1 @ ( k5_relat_1 @ sk_A @ X0 ) ) @ ( sk_C @ X1 @ ( k5_relat_1 @ sk_A @ X0 ) ) @ X0 @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ sk_A @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k5_relat_1 @ sk_A @ X0 ) ) @ ( sk_F_1 @ ( sk_D @ X1 @ ( k5_relat_1 @ sk_A @ X0 ) ) @ ( sk_C @ X1 @ ( k5_relat_1 @ sk_A @ X0 ) ) @ X0 @ sk_A ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( X7
       != ( k5_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X11 @ X8 @ X5 @ X6 ) @ X11 ) @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X11 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('19',plain,(
    ! [X5: $i,X6: $i,X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X11 ) @ ( k5_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X11 @ X8 @ X5 @ X6 ) @ X11 ) @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
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
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

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
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_F_1 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X3 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_D @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ sk_A @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k5_relat_1 @ sk_A @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k5_relat_1 @ sk_A @ X0 ) ) @ ( sk_D @ X1 @ ( k5_relat_1 @ sk_A @ X0 ) ) ) @ ( k5_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ sk_A @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ sk_A @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k5_relat_1 @ sk_A @ X0 ) ) @ ( sk_D @ X1 @ ( k5_relat_1 @ sk_A @ X0 ) ) ) @ ( k5_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k5_relat_1 @ sk_A @ X0 ) ) @ ( sk_D @ X1 @ ( k5_relat_1 @ sk_A @ X0 ) ) ) @ ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ sk_A @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ sk_A @ X0 ) @ ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ sk_A @ X0 ) @ ( k5_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ sk_A @ X0 ) @ ( k5_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k5_relat_1 @ sk_A @ X0 ) @ ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ sk_A @ X0 ) @ ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ sk_A @ X0 ) @ ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ sk_C_1 ) @ ( k5_relat_1 @ sk_B @ sk_C_1 ) ) ),
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
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gGpiQpcVDH
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 79 iterations in 0.075s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.52  thf(dt_k5_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.52       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X13)
% 0.21/0.52          | ~ (v1_relat_1 @ X14)
% 0.21/0.52          | (v1_relat_1 @ (k5_relat_1 @ X13 @ X14)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.52  thf(t49_relat_1, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( v1_relat_1 @ B ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( v1_relat_1 @ C ) =>
% 0.21/0.52               ( ( r1_tarski @ A @ B ) =>
% 0.21/0.52                 ( r1_tarski @ ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( v1_relat_1 @ A ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( v1_relat_1 @ B ) =>
% 0.21/0.52              ( ![C:$i]:
% 0.21/0.52                ( ( v1_relat_1 @ C ) =>
% 0.21/0.52                  ( ( r1_tarski @ A @ B ) =>
% 0.21/0.52                    ( r1_tarski @
% 0.21/0.52                      ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t49_relat_1])).
% 0.21/0.52  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X13)
% 0.21/0.52          | ~ (v1_relat_1 @ X14)
% 0.21/0.52          | (v1_relat_1 @ (k5_relat_1 @ X13 @ X14)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.52  thf(d3_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.52           ( ![C:$i,D:$i]:
% 0.21/0.52             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.21/0.52               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X1)
% 0.21/0.52          | (r1_tarski @ X1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.52  thf(d8_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( v1_relat_1 @ B ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( v1_relat_1 @ C ) =>
% 0.21/0.52               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 0.21/0.52                 ( ![D:$i,E:$i]:
% 0.21/0.52                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.21/0.52                     ( ?[F:$i]:
% 0.21/0.52                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 0.21/0.52                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X11 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X5)
% 0.21/0.52          | ((X7) != (k5_relat_1 @ X6 @ X5))
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ X8 @ (sk_F_1 @ X11 @ X8 @ X5 @ X6)) @ X6)
% 0.21/0.52          | ~ (r2_hidden @ (k4_tarski @ X8 @ X11) @ X7)
% 0.21/0.52          | ~ (v1_relat_1 @ X7)
% 0.21/0.52          | ~ (v1_relat_1 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i, X8 : $i, X11 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X6)
% 0.21/0.52          | ~ (v1_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 0.21/0.52          | ~ (r2_hidden @ (k4_tarski @ X8 @ X11) @ (k5_relat_1 @ X6 @ X5))
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ X8 @ (sk_F_1 @ X11 @ X8 @ X5 @ X6)) @ X6)
% 0.21/0.52          | ~ (v1_relat_1 @ X5))),
% 0.21/0.52      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.52          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (k4_tarski @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.52              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.52               (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 0.21/0.52             X1)
% 0.21/0.52          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X1)
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (k4_tarski @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.52              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.52               (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 0.21/0.52             X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (k4_tarski @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.52              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.52               (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 0.21/0.52             X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '7'])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((r2_hidden @ 
% 0.21/0.52           (k4_tarski @ (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.52            (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.52             (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 0.21/0.52           X1)
% 0.21/0.52          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X1 @ X2)
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ X2)
% 0.21/0.52          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | (r1_tarski @ (k5_relat_1 @ X0 @ X1) @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (k4_tarski @ (sk_C @ X2 @ (k5_relat_1 @ X0 @ X1)) @ 
% 0.21/0.52              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X0 @ X1)) @ 
% 0.21/0.52               (sk_C @ X2 @ (k5_relat_1 @ X0 @ X1)) @ X1 @ X0)) @ 
% 0.21/0.52             X3)
% 0.21/0.52          | ~ (r1_tarski @ X0 @ X3))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X0 @ X3)
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (k4_tarski @ (sk_C @ X2 @ (k5_relat_1 @ X0 @ X1)) @ 
% 0.21/0.52              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X0 @ X1)) @ 
% 0.21/0.52               (sk_C @ X2 @ (k5_relat_1 @ X0 @ X1)) @ X1 @ X0)) @ 
% 0.21/0.52             X3)
% 0.21/0.52          | (r1_tarski @ (k5_relat_1 @ X0 @ X1) @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ sk_A)
% 0.21/0.52          | (r1_tarski @ (k5_relat_1 @ sk_A @ X0) @ X1)
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (k4_tarski @ (sk_C @ X1 @ (k5_relat_1 @ sk_A @ X0)) @ 
% 0.21/0.52              (sk_F_1 @ (sk_D @ X1 @ (k5_relat_1 @ sk_A @ X0)) @ 
% 0.21/0.52               (sk_C @ X1 @ (k5_relat_1 @ sk_A @ X0)) @ X0 @ sk_A)) @ 
% 0.21/0.52             sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '12'])).
% 0.21/0.52  thf('14', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | (r1_tarski @ (k5_relat_1 @ sk_A @ X0) @ X1)
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (k4_tarski @ (sk_C @ X1 @ (k5_relat_1 @ sk_A @ X0)) @ 
% 0.21/0.52              (sk_F_1 @ (sk_D @ X1 @ (k5_relat_1 @ sk_A @ X0)) @ 
% 0.21/0.52               (sk_C @ X1 @ (k5_relat_1 @ sk_A @ X0)) @ X0 @ sk_A)) @ 
% 0.21/0.52             sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X13)
% 0.21/0.52          | ~ (v1_relat_1 @ X14)
% 0.21/0.52          | (v1_relat_1 @ (k5_relat_1 @ X13 @ X14)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X1)
% 0.21/0.52          | (r1_tarski @ X1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X11 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X5)
% 0.21/0.52          | ((X7) != (k5_relat_1 @ X6 @ X5))
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ (sk_F_1 @ X11 @ X8 @ X5 @ X6) @ X11) @ X5)
% 0.21/0.52          | ~ (r2_hidden @ (k4_tarski @ X8 @ X11) @ X7)
% 0.21/0.52          | ~ (v1_relat_1 @ X7)
% 0.21/0.52          | ~ (v1_relat_1 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i, X8 : $i, X11 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X6)
% 0.21/0.52          | ~ (v1_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 0.21/0.52          | ~ (r2_hidden @ (k4_tarski @ X8 @ X11) @ (k5_relat_1 @ X6 @ X5))
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ (sk_F_1 @ X11 @ X8 @ X5 @ X6) @ X11) @ X5)
% 0.21/0.52          | ~ (v1_relat_1 @ X5))),
% 0.21/0.52      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.52          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (k4_tarski @ 
% 0.21/0.52              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.52               (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.21/0.52              (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.21/0.52             X0)
% 0.21/0.52          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['17', '19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X1)
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (k4_tarski @ 
% 0.21/0.52              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.52               (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.21/0.52              (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.21/0.52             X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (k4_tarski @ 
% 0.21/0.52              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.52               (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.21/0.52              (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.21/0.52             X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '21'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((r2_hidden @ 
% 0.21/0.52           (k4_tarski @ 
% 0.21/0.52            (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.52             (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.21/0.52            (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.21/0.52           X0)
% 0.21/0.52          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X13)
% 0.21/0.52          | ~ (v1_relat_1 @ X14)
% 0.21/0.52          | (v1_relat_1 @ (k5_relat_1 @ X13 @ X14)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X5)
% 0.21/0.52          | ((X7) != (k5_relat_1 @ X6 @ X5))
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ X8 @ X9) @ X7)
% 0.21/0.52          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ X6)
% 0.21/0.52          | ~ (r2_hidden @ (k4_tarski @ X10 @ X9) @ X5)
% 0.21/0.52          | ~ (v1_relat_1 @ X7)
% 0.21/0.52          | ~ (v1_relat_1 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X6)
% 0.21/0.52          | ~ (v1_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 0.21/0.52          | ~ (r2_hidden @ (k4_tarski @ X10 @ X9) @ X5)
% 0.21/0.52          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ X6)
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ X8 @ X9) @ (k5_relat_1 @ X6 @ X5))
% 0.21/0.52          | ~ (v1_relat_1 @ X5))),
% 0.21/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.52          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 0.21/0.52          | ~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['24', '26'])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.52         (~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 0.21/0.52          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X3)
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (k4_tarski @ X4 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.21/0.52             (k5_relat_1 @ X3 @ X0))
% 0.21/0.52          | ~ (r2_hidden @ 
% 0.21/0.52               (k4_tarski @ X4 @ 
% 0.21/0.52                (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.52                 (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 0.21/0.52               X3))),
% 0.21/0.52      inference('sup-', [status(thm)], ['23', '28'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.52         (~ (r2_hidden @ 
% 0.21/0.52             (k4_tarski @ X4 @ 
% 0.21/0.52              (sk_F_1 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.21/0.52               (sk_C @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 0.21/0.52             X3)
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (k4_tarski @ X4 @ (sk_D @ X2 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.21/0.52             (k5_relat_1 @ X3 @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X3)
% 0.21/0.52          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r1_tarski @ (k5_relat_1 @ sk_A @ X0) @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ sk_A)
% 0.21/0.52          | (r1_tarski @ (k5_relat_1 @ sk_A @ X0) @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ sk_B)
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (k4_tarski @ (sk_C @ X1 @ (k5_relat_1 @ sk_A @ X0)) @ 
% 0.21/0.52              (sk_D @ X1 @ (k5_relat_1 @ sk_A @ X0))) @ 
% 0.21/0.52             (k5_relat_1 @ sk_B @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['15', '30'])).
% 0.21/0.52  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r1_tarski @ (k5_relat_1 @ sk_A @ X0) @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | (r1_tarski @ (k5_relat_1 @ sk_A @ X0) @ X1)
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (k4_tarski @ (sk_C @ X1 @ (k5_relat_1 @ sk_A @ X0)) @ 
% 0.21/0.52              (sk_D @ X1 @ (k5_relat_1 @ sk_A @ X0))) @ 
% 0.21/0.52             (k5_relat_1 @ sk_B @ X0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_hidden @ 
% 0.21/0.52           (k4_tarski @ (sk_C @ X1 @ (k5_relat_1 @ sk_A @ X0)) @ 
% 0.21/0.52            (sk_D @ X1 @ (k5_relat_1 @ sk_A @ X0))) @ 
% 0.21/0.52           (k5_relat_1 @ sk_B @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | (r1_tarski @ (k5_relat_1 @ sk_A @ X0) @ X1))),
% 0.21/0.52      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X0)
% 0.21/0.52          | (r1_tarski @ X1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r1_tarski @ (k5_relat_1 @ sk_A @ X0) @ (k5_relat_1 @ sk_B @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ X0))
% 0.21/0.52          | (r1_tarski @ (k5_relat_1 @ sk_A @ X0) @ (k5_relat_1 @ sk_B @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | (r1_tarski @ (k5_relat_1 @ sk_A @ X0) @ (k5_relat_1 @ sk_B @ X0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ sk_A)
% 0.21/0.52          | (r1_tarski @ (k5_relat_1 @ sk_A @ X0) @ (k5_relat_1 @ sk_B @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '38'])).
% 0.21/0.52  thf('40', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | (r1_tarski @ (k5_relat_1 @ sk_A @ X0) @ (k5_relat_1 @ sk_B @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r1_tarski @ (k5_relat_1 @ sk_A @ X0) @ (k5_relat_1 @ sk_B @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['41'])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ sk_C_1) @ 
% 0.21/0.52          (k5_relat_1 @ sk_B @ sk_C_1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('44', plain, (~ (v1_relat_1 @ sk_C_1)),
% 0.21/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.52  thf('45', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('46', plain, ($false), inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

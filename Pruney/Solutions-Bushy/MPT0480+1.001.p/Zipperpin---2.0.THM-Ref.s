%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0480+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B6Lhmo8vsP

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 447 expanded)
%              Number of leaves         :   15 ( 132 expanded)
%              Depth                    :   16
%              Number of atoms          : 1023 (6067 expanded)
%              Number of equality atoms :   15 (  81 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t75_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( v1_relat_1 @ D )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ D @ ( k6_relat_1 @ C ) ) )
      <=> ( ( r2_hidden @ B @ C )
          & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( v1_relat_1 @ D )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ D @ ( k6_relat_1 @ C ) ) )
        <=> ( ( r2_hidden @ B @ C )
            & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_relat_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_D_2 )
    | ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['3'])).

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

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( X7
       != ( k5_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X11 @ X8 @ X5 @ X6 ) @ X11 ) @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X11 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('6',plain,(
    ! [X5: $i,X6: $i,X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X11 ) @ ( k5_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X11 @ X8 @ X5 @ X6 ) @ X11 ) @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_B @ sk_A @ ( k6_relat_1 @ sk_C_1 ) @ sk_D_2 ) @ sk_B ) @ ( k6_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) )
      | ~ ( v1_relat_1 @ sk_D_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_B @ sk_A @ ( k6_relat_1 @ sk_C_1 ) @ sk_D_2 ) @ sk_B ) @ ( k6_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,
    ( ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_B @ sk_A @ ( k6_relat_1 @ sk_C_1 ) @ sk_D_2 ) @ sk_B ) @ ( k6_relat_1 @ sk_C_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_B @ sk_A @ ( k6_relat_1 @ sk_C_1 ) @ sk_D_2 ) @ sk_B ) @ ( k6_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_B @ sk_A @ ( k6_relat_1 @ sk_C_1 ) @ sk_D_2 ) @ sk_B ) @ ( k6_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(d10_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ! [C: $i,D: $i] :
            ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
          <=> ( ( r2_hidden @ C @ A )
              & ( C = D ) ) ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k6_relat_1 @ X1 ) )
      | ( X2 = X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k6_relat_1 @ X1 ) )
      | ( X2 = X3 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k6_relat_1 @ X1 ) )
      | ( X2 = X3 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( sk_F_1 @ sk_B @ sk_A @ ( k6_relat_1 @ sk_C_1 ) @ sk_D_2 )
      = sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_B ) @ ( k6_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('25',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('30',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('31',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( X7
       != ( k5_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_F_1 @ X11 @ X8 @ X5 @ X6 ) ) @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X11 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('32',plain,(
    ! [X5: $i,X6: $i,X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X11 ) @ ( k5_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_F_1 @ X11 @ X8 @ X5 @ X6 ) ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_F_1 @ sk_B @ sk_A @ ( k6_relat_1 @ sk_C_1 ) @ sk_D_2 ) ) @ sk_D_2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) )
      | ~ ( v1_relat_1 @ sk_D_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('35',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_F_1 @ sk_B @ sk_A @ ( k6_relat_1 @ sk_C_1 ) @ sk_D_2 ) ) @ sk_D_2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_F_1 @ sk_B @ sk_A @ ( k6_relat_1 @ sk_C_1 ) @ sk_D_2 ) ) @ sk_D_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('39',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_F_1 @ sk_B @ sk_A @ ( k6_relat_1 @ sk_C_1 ) @ sk_D_2 ) ) @ sk_D_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( ( sk_F_1 @ sk_B @ sk_A @ ( k6_relat_1 @ sk_C_1 ) @ sk_D_2 )
      = sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('42',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_D_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_D_2 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_D_2 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) )
    | ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['28','44','45'])).

thf('47',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf('48',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_D_2 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_D_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_D_2 ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_D_2 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['48'])).

thf('51',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_D_2 ),
    inference('sat_resolution*',[status(thm)],['28','44','45','50'])).

thf('52',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_D_2 ),
    inference(simpl_trail,[status(thm)],['49','51'])).

thf('53',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( X0
       != ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X4 ) @ X0 )
      | ( X2 != X4 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('55',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X4 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('57',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X4 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_B ) @ ( k6_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['53','57'])).

thf('59',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('60',plain,(
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

thf('61',plain,(
    ! [X5: $i,X6: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X9 ) @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ X6 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ ( k5_relat_1 @ X6 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C_1 ) )
        | ~ ( v1_relat_1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ sk_C_1 ) ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ X0 ) )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('66',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ sk_C_1 ) ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ X0 ) )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('68',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['28','44','45','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ sk_C_1 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['66','68'])).

thf('70',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['52','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_D_2 @ ( k6_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['47','72'])).


%------------------------------------------------------------------------------

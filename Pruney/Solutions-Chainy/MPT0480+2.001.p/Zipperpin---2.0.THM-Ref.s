%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.27G32xlR8L

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:57 EST 2020

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
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.27G32xlR8L
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 98 iterations in 0.076s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.54  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.21/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.54  thf(t75_relat_1, conjecture,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ D ) =>
% 0.21/0.54       ( ( r2_hidden @
% 0.21/0.54           ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ D @ ( k6_relat_1 @ C ) ) ) <=>
% 0.21/0.54         ( ( r2_hidden @ B @ C ) & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54        ( ( v1_relat_1 @ D ) =>
% 0.21/0.54          ( ( r2_hidden @
% 0.21/0.54              ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ D @ ( k6_relat_1 @ C ) ) ) <=>
% 0.21/0.54            ( ( r2_hidden @ B @ C ) & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t75_relat_1])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_D_2)
% 0.21/0.54        | ~ (r2_hidden @ sk_B @ sk_C_1)
% 0.21/0.54        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54             (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54           (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1))))
% 0.21/0.54         <= (~
% 0.21/0.54             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54               (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf(dt_k5_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.54       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X13)
% 0.21/0.54          | ~ (v1_relat_1 @ X14)
% 0.21/0.54          | (v1_relat_1 @ (k5_relat_1 @ X13 @ X14)))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ sk_C_1)
% 0.21/0.54        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54           (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54         (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1))))
% 0.21/0.54         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54               (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))))),
% 0.21/0.54      inference('split', [status(esa)], ['3'])).
% 0.21/0.54  thf(d8_relat_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( v1_relat_1 @ B ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( v1_relat_1 @ C ) =>
% 0.21/0.54               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 0.21/0.54                 ( ![D:$i,E:$i]:
% 0.21/0.54                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.21/0.54                     ( ?[F:$i]:
% 0.21/0.54                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 0.21/0.54                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X11 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X5)
% 0.21/0.54          | ((X7) != (k5_relat_1 @ X6 @ X5))
% 0.21/0.54          | (r2_hidden @ (k4_tarski @ (sk_F_1 @ X11 @ X8 @ X5 @ X6) @ X11) @ X5)
% 0.21/0.54          | ~ (r2_hidden @ (k4_tarski @ X8 @ X11) @ X7)
% 0.21/0.54          | ~ (v1_relat_1 @ X7)
% 0.21/0.54          | ~ (v1_relat_1 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X5 : $i, X6 : $i, X8 : $i, X11 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X6)
% 0.21/0.54          | ~ (v1_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 0.21/0.54          | ~ (r2_hidden @ (k4_tarski @ X8 @ X11) @ (k5_relat_1 @ X6 @ X5))
% 0.21/0.54          | (r2_hidden @ (k4_tarski @ (sk_F_1 @ X11 @ X8 @ X5 @ X6) @ X11) @ X5)
% 0.21/0.54          | ~ (v1_relat_1 @ X5))),
% 0.21/0.54      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (((~ (v1_relat_1 @ (k6_relat_1 @ sk_C_1))
% 0.21/0.54         | (r2_hidden @ 
% 0.21/0.54            (k4_tarski @ 
% 0.21/0.54             (sk_F_1 @ sk_B @ sk_A @ (k6_relat_1 @ sk_C_1) @ sk_D_2) @ sk_B) @ 
% 0.21/0.54            (k6_relat_1 @ sk_C_1))
% 0.21/0.54         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))
% 0.21/0.54         | ~ (v1_relat_1 @ sk_D_2)))
% 0.21/0.54         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54               (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.54  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.21/0.54  thf('8', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.54  thf('9', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      ((((r2_hidden @ 
% 0.21/0.54          (k4_tarski @ 
% 0.21/0.54           (sk_F_1 @ sk_B @ sk_A @ (k6_relat_1 @ sk_C_1) @ sk_D_2) @ sk_B) @ 
% 0.21/0.54          (k6_relat_1 @ sk_C_1))
% 0.21/0.54         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))))
% 0.21/0.54         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54               (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))))),
% 0.21/0.54      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (((~ (v1_relat_1 @ (k6_relat_1 @ sk_C_1))
% 0.21/0.54         | ~ (v1_relat_1 @ sk_D_2)
% 0.21/0.54         | (r2_hidden @ 
% 0.21/0.54            (k4_tarski @ 
% 0.21/0.54             (sk_F_1 @ sk_B @ sk_A @ (k6_relat_1 @ sk_C_1) @ sk_D_2) @ sk_B) @ 
% 0.21/0.54            (k6_relat_1 @ sk_C_1))))
% 0.21/0.54         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54               (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['2', '10'])).
% 0.21/0.54  thf('12', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.54  thf('13', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (((r2_hidden @ 
% 0.21/0.54         (k4_tarski @ 
% 0.21/0.54          (sk_F_1 @ sk_B @ sk_A @ (k6_relat_1 @ sk_C_1) @ sk_D_2) @ sk_B) @ 
% 0.21/0.54         (k6_relat_1 @ sk_C_1)))
% 0.21/0.54         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54               (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))))),
% 0.21/0.54      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (((r2_hidden @ 
% 0.21/0.54         (k4_tarski @ 
% 0.21/0.54          (sk_F_1 @ sk_B @ sk_A @ (k6_relat_1 @ sk_C_1) @ sk_D_2) @ sk_B) @ 
% 0.21/0.54         (k6_relat_1 @ sk_C_1)))
% 0.21/0.54         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54               (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))))),
% 0.21/0.54      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.21/0.54  thf(d10_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ B ) =>
% 0.21/0.54       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.21/0.54         ( ![C:$i,D:$i]:
% 0.21/0.54           ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.21/0.54             ( ( r2_hidden @ C @ A ) & ( ( C ) = ( D ) ) ) ) ) ) ))).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.54         (((X0) != (k6_relat_1 @ X1))
% 0.21/0.54          | ((X2) = (X3))
% 0.21/0.54          | ~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_relat_1])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.21/0.54          | ~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k6_relat_1 @ X1))
% 0.21/0.54          | ((X2) = (X3)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.54  thf('18', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.54         (~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k6_relat_1 @ X1))
% 0.21/0.54          | ((X2) = (X3)))),
% 0.21/0.54      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      ((((sk_F_1 @ sk_B @ sk_A @ (k6_relat_1 @ sk_C_1) @ sk_D_2) = (sk_B)))
% 0.21/0.54         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54               (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['15', '19'])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (((r2_hidden @ (k4_tarski @ sk_B @ sk_B) @ (k6_relat_1 @ sk_C_1)))
% 0.21/0.54         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54               (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))))),
% 0.21/0.54      inference('demod', [status(thm)], ['14', '20'])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.54         (((X0) != (k6_relat_1 @ X1))
% 0.21/0.54          | (r2_hidden @ X2 @ X1)
% 0.21/0.54          | ~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_relat_1])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.21/0.54          | ~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k6_relat_1 @ X1))
% 0.21/0.54          | (r2_hidden @ X2 @ X1))),
% 0.21/0.54      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.54  thf('24', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.54         (~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k6_relat_1 @ X1))
% 0.21/0.54          | (r2_hidden @ X2 @ X1))),
% 0.21/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ sk_C_1))
% 0.21/0.54         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54               (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['21', '25'])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      ((~ (r2_hidden @ sk_B @ sk_C_1)) <= (~ ((r2_hidden @ sk_B @ sk_C_1)))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ sk_C_1)) | 
% 0.21/0.54       ~
% 0.21/0.54       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54         (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X13)
% 0.21/0.54          | ~ (v1_relat_1 @ X14)
% 0.21/0.54          | (v1_relat_1 @ (k5_relat_1 @ X13 @ X14)))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54         (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1))))
% 0.21/0.54         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54               (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))))),
% 0.21/0.54      inference('split', [status(esa)], ['3'])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X11 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X5)
% 0.21/0.54          | ((X7) != (k5_relat_1 @ X6 @ X5))
% 0.21/0.54          | (r2_hidden @ (k4_tarski @ X8 @ (sk_F_1 @ X11 @ X8 @ X5 @ X6)) @ X6)
% 0.21/0.54          | ~ (r2_hidden @ (k4_tarski @ X8 @ X11) @ X7)
% 0.21/0.54          | ~ (v1_relat_1 @ X7)
% 0.21/0.54          | ~ (v1_relat_1 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X5 : $i, X6 : $i, X8 : $i, X11 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X6)
% 0.21/0.54          | ~ (v1_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 0.21/0.54          | ~ (r2_hidden @ (k4_tarski @ X8 @ X11) @ (k5_relat_1 @ X6 @ X5))
% 0.21/0.54          | (r2_hidden @ (k4_tarski @ X8 @ (sk_F_1 @ X11 @ X8 @ X5 @ X6)) @ X6)
% 0.21/0.54          | ~ (v1_relat_1 @ X5))),
% 0.21/0.54      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (((~ (v1_relat_1 @ (k6_relat_1 @ sk_C_1))
% 0.21/0.54         | (r2_hidden @ 
% 0.21/0.54            (k4_tarski @ sk_A @ 
% 0.21/0.54             (sk_F_1 @ sk_B @ sk_A @ (k6_relat_1 @ sk_C_1) @ sk_D_2)) @ 
% 0.21/0.54            sk_D_2)
% 0.21/0.54         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))
% 0.21/0.54         | ~ (v1_relat_1 @ sk_D_2)))
% 0.21/0.54         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54               (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['30', '32'])).
% 0.21/0.54  thf('34', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.54  thf('35', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      ((((r2_hidden @ 
% 0.21/0.54          (k4_tarski @ sk_A @ 
% 0.21/0.54           (sk_F_1 @ sk_B @ sk_A @ (k6_relat_1 @ sk_C_1) @ sk_D_2)) @ 
% 0.21/0.54          sk_D_2)
% 0.21/0.54         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))))
% 0.21/0.54         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54               (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))))),
% 0.21/0.54      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (((~ (v1_relat_1 @ (k6_relat_1 @ sk_C_1))
% 0.21/0.54         | ~ (v1_relat_1 @ sk_D_2)
% 0.21/0.54         | (r2_hidden @ 
% 0.21/0.54            (k4_tarski @ sk_A @ 
% 0.21/0.54             (sk_F_1 @ sk_B @ sk_A @ (k6_relat_1 @ sk_C_1) @ sk_D_2)) @ 
% 0.21/0.54            sk_D_2)))
% 0.21/0.54         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54               (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['29', '36'])).
% 0.21/0.54  thf('38', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.54  thf('39', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (((r2_hidden @ 
% 0.21/0.54         (k4_tarski @ sk_A @ 
% 0.21/0.54          (sk_F_1 @ sk_B @ sk_A @ (k6_relat_1 @ sk_C_1) @ sk_D_2)) @ 
% 0.21/0.54         sk_D_2))
% 0.21/0.54         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54               (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))))),
% 0.21/0.54      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      ((((sk_F_1 @ sk_B @ sk_A @ (k6_relat_1 @ sk_C_1) @ sk_D_2) = (sk_B)))
% 0.21/0.54         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54               (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['15', '19'])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_D_2))
% 0.21/0.54         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54               (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))))),
% 0.21/0.54      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_D_2))
% 0.21/0.54         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_D_2)))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_D_2)) | 
% 0.21/0.54       ~
% 0.21/0.54       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54         (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (~
% 0.21/0.54       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54         (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))) | 
% 0.21/0.54       ~ ((r2_hidden @ sk_B @ sk_C_1)) | 
% 0.21/0.54       ~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_D_2))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (~
% 0.21/0.54       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54         (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1))))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['28', '44', '45'])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54          (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['1', '46'])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_D_2)
% 0.21/0.54        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54           (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_D_2))
% 0.21/0.54         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_D_2)))),
% 0.21/0.54      inference('split', [status(esa)], ['48'])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_D_2)) | 
% 0.21/0.54       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54         (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1))))),
% 0.21/0.54      inference('split', [status(esa)], ['48'])).
% 0.21/0.54  thf('51', plain, (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_D_2))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['28', '44', '45', '50'])).
% 0.21/0.54  thf('52', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_D_2)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['49', '51'])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ sk_C_1)) <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 0.21/0.54      inference('split', [status(esa)], ['3'])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.54         (((X0) != (k6_relat_1 @ X1))
% 0.21/0.54          | (r2_hidden @ (k4_tarski @ X2 @ X4) @ X0)
% 0.21/0.54          | ((X2) != (X4))
% 0.21/0.54          | ~ (r2_hidden @ X2 @ X1)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_relat_1])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      (![X1 : $i, X4 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.21/0.54          | ~ (r2_hidden @ X4 @ X1)
% 0.21/0.54          | (r2_hidden @ (k4_tarski @ X4 @ X4) @ (k6_relat_1 @ X1)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['54'])).
% 0.21/0.54  thf('56', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      (![X1 : $i, X4 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X4 @ X1)
% 0.21/0.54          | (r2_hidden @ (k4_tarski @ X4 @ X4) @ (k6_relat_1 @ X1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      (((r2_hidden @ (k4_tarski @ sk_B @ sk_B) @ (k6_relat_1 @ sk_C_1)))
% 0.21/0.54         <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['53', '57'])).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X13)
% 0.21/0.54          | ~ (v1_relat_1 @ X14)
% 0.21/0.54          | (v1_relat_1 @ (k5_relat_1 @ X13 @ X14)))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X5)
% 0.21/0.54          | ((X7) != (k5_relat_1 @ X6 @ X5))
% 0.21/0.54          | (r2_hidden @ (k4_tarski @ X8 @ X9) @ X7)
% 0.21/0.54          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ X6)
% 0.21/0.54          | ~ (r2_hidden @ (k4_tarski @ X10 @ X9) @ X5)
% 0.21/0.54          | ~ (v1_relat_1 @ X7)
% 0.21/0.54          | ~ (v1_relat_1 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.21/0.54  thf('61', plain,
% 0.21/0.54      (![X5 : $i, X6 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X6)
% 0.21/0.54          | ~ (v1_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 0.21/0.54          | ~ (r2_hidden @ (k4_tarski @ X10 @ X9) @ X5)
% 0.21/0.54          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ X6)
% 0.21/0.54          | (r2_hidden @ (k4_tarski @ X8 @ X9) @ (k5_relat_1 @ X6 @ X5))
% 0.21/0.54          | ~ (v1_relat_1 @ X5))),
% 0.21/0.54      inference('simplify', [status(thm)], ['60'])).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X1)
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.54          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 0.21/0.54          | ~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['59', '61'])).
% 0.21/0.54  thf('63', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.54         (~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 0.21/0.54          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 0.21/0.54          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ X1)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['62'])).
% 0.21/0.54  thf('64', plain,
% 0.21/0.54      ((![X0 : $i, X1 : $i]:
% 0.21/0.54          (~ (v1_relat_1 @ (k6_relat_1 @ sk_C_1))
% 0.21/0.54           | ~ (v1_relat_1 @ X0)
% 0.21/0.54           | (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ 
% 0.21/0.54              (k5_relat_1 @ X0 @ (k6_relat_1 @ sk_C_1)))
% 0.21/0.54           | ~ (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ X0)))
% 0.21/0.54         <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['58', '63'])).
% 0.21/0.54  thf('65', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.54  thf('66', plain,
% 0.21/0.54      ((![X0 : $i, X1 : $i]:
% 0.21/0.54          (~ (v1_relat_1 @ X0)
% 0.21/0.54           | (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ 
% 0.21/0.54              (k5_relat_1 @ X0 @ (k6_relat_1 @ sk_C_1)))
% 0.21/0.54           | ~ (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ X0)))
% 0.21/0.54         <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['64', '65'])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ sk_C_1)) | 
% 0.21/0.54       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54         (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1))))),
% 0.21/0.54      inference('split', [status(esa)], ['3'])).
% 0.21/0.54  thf('68', plain, (((r2_hidden @ sk_B @ sk_C_1))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['28', '44', '45', '67'])).
% 0.21/0.54  thf('69', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ 
% 0.21/0.54             (k5_relat_1 @ X0 @ (k6_relat_1 @ sk_C_1)))
% 0.21/0.54          | ~ (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ X0))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['66', '68'])).
% 0.21/0.54  thf('70', plain,
% 0.21/0.54      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54         (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))
% 0.21/0.54        | ~ (v1_relat_1 @ sk_D_2))),
% 0.21/0.54      inference('sup-', [status(thm)], ['52', '69'])).
% 0.21/0.54  thf('71', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('72', plain,
% 0.21/0.54      ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.54        (k5_relat_1 @ sk_D_2 @ (k6_relat_1 @ sk_C_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['70', '71'])).
% 0.21/0.54  thf('73', plain, ($false), inference('demod', [status(thm)], ['47', '72'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

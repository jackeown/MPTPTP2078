%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0626+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xRaUdYMjdP

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:13 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 232 expanded)
%              Number of leaves         :   18 (  70 expanded)
%              Depth                    :   18
%              Number of atoms          : 1211 (3784 expanded)
%              Number of equality atoms :   15 (  41 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(t21_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
          <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
              & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
            <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
                & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t21_funct_1])).

thf('0',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D_1 @ X8 @ X6 ) ) @ X6 )
      | ( X7
       != ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('6',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D_1 @ X8 @ X6 ) ) @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

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

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( X13
       != ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) @ X17 ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('9',plain,(
    ! [X11: $i,X12: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) @ X17 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) @ sk_A @ sk_B @ sk_C_1 ) @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) @ sk_A @ sk_B @ sk_C_1 ) @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( X13
       != ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) ) @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('17',plain,(
    ! [X11: $i,X12: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_F_1 @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_F_1 @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_F_1 @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_F_1 @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_F_1 @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('27',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('28',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X3
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C_1 )
        | ~ ( v1_funct_1 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_1 )
        | ( X0
          = ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_1 )
        | ( X0
          = ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( ( sk_F_1 @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) @ sk_A @ sk_B @ sk_C_1 )
      = ( k1_funct_1 @ sk_C_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','35'])).

thf('37',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('42',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['43'])).

thf('47',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ( X3
       != ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('56',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) @ sk_B )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('61',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( X13
       != ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X15 ) @ X11 )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('62',plain,(
    ! [X11: $i,X12: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X15 ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ sk_B )
        | ~ ( v1_relat_1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) @ ( k5_relat_1 @ X0 @ sk_B ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) @ X0 ) )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) @ ( k5_relat_1 @ X0 @ sk_B ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) @ X0 ) )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['53','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('72',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('74',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('76',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('77',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['43'])).

thf('78',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','45','46','74','75','78'])).


%------------------------------------------------------------------------------

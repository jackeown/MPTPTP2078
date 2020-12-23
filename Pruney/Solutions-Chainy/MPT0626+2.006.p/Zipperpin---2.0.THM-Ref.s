%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NTQQaXBzX6

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 182 expanded)
%              Number of leaves         :   18 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  804 (2745 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

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
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) )
        = ( k10_relat_1 @ X5 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X1 @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('10',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( sk_D @ sk_C @ ( k1_relat_1 @ sk_B ) @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ ( k1_relat_1 @ sk_B ) @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k10_relat_1 @ X3 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_D @ X3 @ X1 @ X2 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('15',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D @ sk_C @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D @ sk_C @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) @ sk_C )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ X10 )
      | ( X11
        = ( k1_funct_1 @ X10 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('19',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( sk_D @ sk_C @ ( k1_relat_1 @ sk_B ) @ sk_A )
        = ( k1_funct_1 @ sk_C @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( sk_D @ sk_C @ ( k1_relat_1 @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_C @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['24'])).

thf('28',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X10 ) )
      | ( X11
       != ( k1_funct_1 @ X10 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X9 @ ( k1_funct_1 @ X10 @ X9 ) ) @ X10 )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ sk_C )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ X3 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ X3 ) )
      | ( r2_hidden @ X2 @ ( k10_relat_1 @ X3 @ X1 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) )
        | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
        | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) )
        | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
        | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ sk_C )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('41',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X8 )
      | ( r2_hidden @ X7 @ ( k2_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('42',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) )
        | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_B ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','45'])).

thf('47',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) )
        = ( k10_relat_1 @ X5 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(split,[status(esa)],['24'])).

thf('49',plain,
    ( ( ~ ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('55',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D @ sk_C @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) @ sk_C )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('56',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X8 )
      | ( r2_hidden @ X6 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('57',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('61',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','26','27','53','54','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NTQQaXBzX6
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:39:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 64 iterations in 0.053s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.51  thf(t21_funct_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.51       ( ![C:$i]:
% 0.21/0.51         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.51           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.21/0.51             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.51               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i]:
% 0.21/0.51        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.51          ( ![C:$i]:
% 0.21/0.51            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.51              ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.21/0.51                ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.51                  ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t21_funct_1])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.21/0.51        | (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))) | 
% 0.21/0.51       ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf(t182_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( v1_relat_1 @ B ) =>
% 0.21/0.51           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.51             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X4)
% 0.21/0.51          | ((k1_relat_1 @ (k5_relat_1 @ X5 @ X4))
% 0.21/0.51              = (k10_relat_1 @ X5 @ (k1_relat_1 @ X4)))
% 0.21/0.51          | ~ (v1_relat_1 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))
% 0.21/0.51        | (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.21/0.51      inference('split', [status(esa)], ['3'])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      ((((r2_hidden @ sk_A @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_B)))
% 0.21/0.51         | ~ (v1_relat_1 @ sk_C)
% 0.21/0.51         | ~ (v1_relat_1 @ sk_B)))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['2', '4'])).
% 0.21/0.51  thf('6', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (((r2_hidden @ sk_A @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_B))))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.21/0.51      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.51  thf(t166_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ C ) =>
% 0.21/0.51       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.21/0.51         ( ?[D:$i]:
% 0.21/0.51           ( ( r2_hidden @ D @ B ) & 
% 0.21/0.51             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.21/0.51             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X2 @ (k10_relat_1 @ X3 @ X1))
% 0.21/0.51          | (r2_hidden @ (sk_D @ X3 @ X1 @ X2) @ X1)
% 0.21/0.51          | ~ (v1_relat_1 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (((~ (v1_relat_1 @ sk_C)
% 0.21/0.51         | (r2_hidden @ (sk_D @ sk_C @ (k1_relat_1 @ sk_B) @ sk_A) @ 
% 0.21/0.51            (k1_relat_1 @ sk_B))))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.51  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (((r2_hidden @ (sk_D @ sk_C @ (k1_relat_1 @ sk_B) @ sk_A) @ 
% 0.21/0.51         (k1_relat_1 @ sk_B)))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (((r2_hidden @ sk_A @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_B))))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.21/0.51      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X2 @ (k10_relat_1 @ X3 @ X1))
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X2 @ (sk_D @ X3 @ X1 @ X2)) @ X3)
% 0.21/0.51          | ~ (v1_relat_1 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (((~ (v1_relat_1 @ sk_C)
% 0.21/0.51         | (r2_hidden @ 
% 0.21/0.51            (k4_tarski @ sk_A @ (sk_D @ sk_C @ (k1_relat_1 @ sk_B) @ sk_A)) @ 
% 0.21/0.51            sk_C)))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (((r2_hidden @ 
% 0.21/0.51         (k4_tarski @ sk_A @ (sk_D @ sk_C @ (k1_relat_1 @ sk_B) @ sk_A)) @ sk_C))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.21/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf(t8_funct_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.51       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.21/0.51         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.51           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.51         (~ (r2_hidden @ (k4_tarski @ X9 @ X11) @ X10)
% 0.21/0.51          | ((X11) = (k1_funct_1 @ X10 @ X9))
% 0.21/0.51          | ~ (v1_funct_1 @ X10)
% 0.21/0.51          | ~ (v1_relat_1 @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (((~ (v1_relat_1 @ sk_C)
% 0.21/0.51         | ~ (v1_funct_1 @ sk_C)
% 0.21/0.51         | ((sk_D @ sk_C @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.21/0.51             = (k1_funct_1 @ sk_C @ sk_A))))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      ((((sk_D @ sk_C @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.21/0.51          = (k1_funct_1 @ sk_C @ sk_A)))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.21/0.51      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B)))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      ((~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.21/0.51        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))
% 0.21/0.51        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      ((~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B)))
% 0.21/0.51         <= (~ ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 0.21/0.51      inference('split', [status(esa)], ['24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))) | 
% 0.21/0.51       ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) | 
% 0.21/0.51       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))) | 
% 0.21/0.51       ~ ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.21/0.51      inference('split', [status(esa)], ['24'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B)))
% 0.21/0.51         <= (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.21/0.51      inference('split', [status(esa)], ['3'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X9 @ (k1_relat_1 @ X10))
% 0.21/0.51          | ((X11) != (k1_funct_1 @ X10 @ X9))
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X9 @ X11) @ X10)
% 0.21/0.51          | ~ (v1_funct_1 @ X10)
% 0.21/0.51          | ~ (v1_relat_1 @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X10)
% 0.21/0.51          | ~ (v1_funct_1 @ X10)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X9 @ (k1_funct_1 @ X10 @ X9)) @ X10)
% 0.21/0.51          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X10)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      ((((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ sk_C)
% 0.21/0.51         | ~ (v1_funct_1 @ sk_C)
% 0.21/0.51         | ~ (v1_relat_1 @ sk_C)))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['29', '31'])).
% 0.21/0.51  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ sk_C))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.21/0.51      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X2 @ X0) @ X3)
% 0.21/0.51          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ X3))
% 0.21/0.51          | (r2_hidden @ X2 @ (k10_relat_1 @ X3 @ X1))
% 0.21/0.51          | ~ (v1_relat_1 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          (~ (v1_relat_1 @ sk_C)
% 0.21/0.51           | (r2_hidden @ sk_A @ (k10_relat_1 @ sk_C @ X0))
% 0.21/0.51           | ~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.21/0.51           | ~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ X0)))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.51  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          ((r2_hidden @ sk_A @ (k10_relat_1 @ sk_C @ X0))
% 0.21/0.51           | ~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.21/0.51           | ~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ X0)))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.21/0.51      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ sk_C))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.21/0.51      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.21/0.51  thf(t20_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ C ) =>
% 0.21/0.51       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.21/0.51         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.51           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.51         (~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ X8)
% 0.21/0.51          | (r2_hidden @ X7 @ (k2_relat_1 @ X8))
% 0.21/0.51          | ~ (v1_relat_1 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (((~ (v1_relat_1 @ sk_C)
% 0.21/0.51         | (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k2_relat_1 @ sk_C))))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k2_relat_1 @ sk_C)))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.21/0.51      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          ((r2_hidden @ sk_A @ (k10_relat_1 @ sk_C @ X0))
% 0.21/0.51           | ~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ X0)))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.21/0.51      inference('demod', [status(thm)], ['39', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (((r2_hidden @ sk_A @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_B))))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) & 
% 0.21/0.51             ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['28', '45'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X4)
% 0.21/0.51          | ((k1_relat_1 @ (k5_relat_1 @ X5 @ X4))
% 0.21/0.51              = (k10_relat_1 @ X5 @ (k1_relat_1 @ X4)))
% 0.21/0.51          | ~ (v1_relat_1 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))))
% 0.21/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.21/0.51      inference('split', [status(esa)], ['24'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (((~ (r2_hidden @ sk_A @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_B)))
% 0.21/0.51         | ~ (v1_relat_1 @ sk_C)
% 0.21/0.51         | ~ (v1_relat_1 @ sk_B)))
% 0.21/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.51  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      ((~ (r2_hidden @ sk_A @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_B))))
% 0.21/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.21/0.51      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))) | 
% 0.21/0.51       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) | 
% 0.21/0.51       ~ ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['46', '52'])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))) | 
% 0.21/0.51       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))),
% 0.21/0.51      inference('split', [status(esa)], ['3'])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (((r2_hidden @ 
% 0.21/0.51         (k4_tarski @ sk_A @ (sk_D @ sk_C @ (k1_relat_1 @ sk_B) @ sk_A)) @ sk_C))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.21/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.51         (~ (r2_hidden @ (k4_tarski @ X6 @ X7) @ X8)
% 0.21/0.51          | (r2_hidden @ X6 @ (k1_relat_1 @ X8))
% 0.21/0.51          | ~ (v1_relat_1 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (((~ (v1_relat_1 @ sk_C) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.51  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))
% 0.21/0.51         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.21/0.51      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))
% 0.21/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.21/0.51      inference('split', [status(esa)], ['24'])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))) | 
% 0.21/0.51       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.51  thf('62', plain, ($false),
% 0.21/0.51      inference('sat_resolution*', [status(thm)],
% 0.21/0.51                ['1', '26', '27', '53', '54', '61'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

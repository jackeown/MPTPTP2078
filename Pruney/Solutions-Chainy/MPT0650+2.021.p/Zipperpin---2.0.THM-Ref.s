%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4DSXVjvP7x

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 271 expanded)
%              Number of leaves         :   21 (  86 expanded)
%              Depth                    :   22
%              Number of atoms          :  921 (4065 expanded)
%              Number of equality atoms :   48 ( 265 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t57_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( v2_funct_1 @ B )
            & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
         => ( ( A
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
            & ( A
              = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_funct_1])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('5',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( X19
       != ( k1_funct_1 @ X18 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ ( k1_funct_1 @ X18 @ X17 ) ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ( X3
       != ( k2_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('21',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['19','21'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 )
      | ( r2_hidden @ X7 @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t56_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X15 ) )
      | ( X16
        = ( k1_funct_1 @ ( k2_funct_1 @ X15 ) @ ( k1_funct_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['19','21'])).

thf('32',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ X18 )
      | ( X19
        = ( k1_funct_1 @ X18 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_A
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30','36','37'])).

thf('39',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B ) ) @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['18','38'])).

thf('40',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 )
      | ( r2_hidden @ X7 @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k1_funct_1 @ X11 @ ( k1_funct_1 @ X12 @ X13 ) ) )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30','36','37'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30','36','37'])).

thf('61',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['58'])).

thf('62',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('64',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['58'])).

thf('67',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['65','66'])).

thf('68',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['59','67'])).

thf('69',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['57','68'])).

thf('70',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('71',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    $false ),
    inference(simplify,[status(thm)],['73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4DSXVjvP7x
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:53:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 81 iterations in 0.068s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.51  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.51  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(dt_k2_funct_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.51       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.20/0.51         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X10 : $i]:
% 0.20/0.51         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 0.20/0.51          | ~ (v1_funct_1 @ X10)
% 0.20/0.51          | ~ (v1_relat_1 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X10 : $i]:
% 0.20/0.51         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.20/0.51          | ~ (v1_funct_1 @ X10)
% 0.20/0.51          | ~ (v1_relat_1 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X10 : $i]:
% 0.20/0.51         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.20/0.51          | ~ (v1_funct_1 @ X10)
% 0.20/0.51          | ~ (v1_relat_1 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.51  thf(t57_funct_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.51       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.20/0.51         ( ( ( A ) =
% 0.20/0.51             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.20/0.51           ( ( A ) =
% 0.20/0.51             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i]:
% 0.20/0.51        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.51          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.20/0.51            ( ( ( A ) =
% 0.20/0.51                ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.20/0.51              ( ( A ) =
% 0.20/0.51                ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t57_funct_1])).
% 0.20/0.51  thf('3', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X10 : $i]:
% 0.20/0.51         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.20/0.51          | ~ (v1_funct_1 @ X10)
% 0.20/0.51          | ~ (v1_relat_1 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X10 : $i]:
% 0.20/0.51         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 0.20/0.51          | ~ (v1_funct_1 @ X10)
% 0.20/0.51          | ~ (v1_relat_1 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.51  thf(t55_funct_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.51       ( ( v2_funct_1 @ A ) =>
% 0.20/0.51         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.20/0.51           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X14 : $i]:
% 0.20/0.51         (~ (v2_funct_1 @ X14)
% 0.20/0.51          | ((k2_relat_1 @ X14) = (k1_relat_1 @ (k2_funct_1 @ X14)))
% 0.20/0.51          | ~ (v1_funct_1 @ X14)
% 0.20/0.51          | ~ (v1_relat_1 @ X14))),
% 0.20/0.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.20/0.51  thf(t8_funct_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.51       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.51         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.51           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X17 @ (k1_relat_1 @ X18))
% 0.20/0.51          | ((X19) != (k1_funct_1 @ X18 @ X17))
% 0.20/0.51          | (r2_hidden @ (k4_tarski @ X17 @ X19) @ X18)
% 0.20/0.51          | ~ (v1_funct_1 @ X18)
% 0.20/0.51          | ~ (v1_relat_1 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X18)
% 0.20/0.51          | ~ (v1_funct_1 @ X18)
% 0.20/0.51          | (r2_hidden @ (k4_tarski @ X17 @ (k1_funct_1 @ X18 @ X17)) @ X18)
% 0.20/0.51          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X18)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.20/0.51          | ~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ~ (v2_funct_1 @ X0)
% 0.20/0.51          | (r2_hidden @ 
% 0.20/0.51             (k4_tarski @ X1 @ (k1_funct_1 @ (k2_funct_1 @ X0) @ X1)) @ 
% 0.20/0.51             (k2_funct_1 @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.20/0.51          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.51          | (r2_hidden @ 
% 0.20/0.51             (k4_tarski @ X1 @ (k1_funct_1 @ (k2_funct_1 @ X0) @ X1)) @ 
% 0.20/0.51             (k2_funct_1 @ X0))
% 0.20/0.51          | ~ (v2_funct_1 @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.20/0.51          | ~ (v2_funct_1 @ X0)
% 0.20/0.51          | (r2_hidden @ 
% 0.20/0.51             (k4_tarski @ X1 @ (k1_funct_1 @ (k2_funct_1 @ X0) @ X1)) @ 
% 0.20/0.51             (k2_funct_1 @ X0))
% 0.20/0.51          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ X0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | (r2_hidden @ 
% 0.20/0.51             (k4_tarski @ X1 @ (k1_funct_1 @ (k2_funct_1 @ X0) @ X1)) @ 
% 0.20/0.51             (k2_funct_1 @ X0))
% 0.20/0.51          | ~ (v2_funct_1 @ X0)
% 0.20/0.51          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.20/0.51          | ~ (v2_funct_1 @ X0)
% 0.20/0.51          | (r2_hidden @ 
% 0.20/0.51             (k4_tarski @ X1 @ (k1_funct_1 @ (k2_funct_1 @ X0) @ X1)) @ 
% 0.20/0.51             (k2_funct_1 @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ X0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.51        | (r2_hidden @ 
% 0.20/0.51           (k4_tarski @ sk_A @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)) @ 
% 0.20/0.51           (k2_funct_1 @ sk_B))
% 0.20/0.51        | ~ (v2_funct_1 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '13'])).
% 0.20/0.51  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('17', plain, ((v2_funct_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      ((r2_hidden @ 
% 0.20/0.51        (k4_tarski @ sk_A @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)) @ 
% 0.20/0.51        (k2_funct_1 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.20/0.51  thf('19', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d5_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.51           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.51          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 0.20/0.51          | ((X3) != (k2_relat_1 @ X2)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X2 : $i, X4 : $i]:
% 0.20/0.51         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 0.20/0.51          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X2)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A @ sk_B) @ sk_A) @ sk_B)),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '21'])).
% 0.20/0.51  thf(t20_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ C ) =>
% 0.20/0.51       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.20/0.51         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.51           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9)
% 0.20/0.51          | (r2_hidden @ X7 @ (k1_relat_1 @ X9))
% 0.20/0.51          | ~ (v1_relat_1 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.51        | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf(t56_funct_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.51       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.20/0.51         ( ( ( A ) =
% 0.20/0.51             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.20/0.51           ( ( A ) =
% 0.20/0.51             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i]:
% 0.20/0.51         (~ (v2_funct_1 @ X15)
% 0.20/0.51          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X15))
% 0.20/0.51          | ((X16)
% 0.20/0.51              = (k1_funct_1 @ (k2_funct_1 @ X15) @ (k1_funct_1 @ X15 @ X16)))
% 0.20/0.51          | ~ (v1_funct_1 @ X15)
% 0.20/0.51          | ~ (v1_relat_1 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t56_funct_1])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.51        | ((sk_D_1 @ sk_A @ sk_B)
% 0.20/0.51            = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.20/0.51               (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 0.20/0.51        | ~ (v2_funct_1 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.51  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('30', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A @ sk_B) @ sk_A) @ sk_B)),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '21'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (k4_tarski @ X17 @ X19) @ X18)
% 0.20/0.51          | ((X19) = (k1_funct_1 @ X18 @ X17))
% 0.20/0.51          | ~ (v1_funct_1 @ X18)
% 0.20/0.51          | ~ (v1_relat_1 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.51        | ((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('35', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('36', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.51  thf('37', plain, ((v2_funct_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['28', '29', '30', '36', '37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B)) @ 
% 0.20/0.51        (k2_funct_1 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['18', '38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9)
% 0.20/0.51          | (r2_hidden @ X7 @ (k1_relat_1 @ X9))
% 0.20/0.51          | ~ (v1_relat_1 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.20/0.51        | (r2_hidden @ sk_A @ (k1_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.51        | (r2_hidden @ sk_A @ (k1_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '41'])).
% 0.20/0.51  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('44', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('45', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.20/0.51  thf(t23_funct_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.51           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.51             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.20/0.51               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X11)
% 0.20/0.51          | ~ (v1_funct_1 @ X11)
% 0.20/0.51          | ((k1_funct_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 0.20/0.51              = (k1_funct_1 @ X11 @ (k1_funct_1 @ X12 @ X13)))
% 0.20/0.51          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X12))
% 0.20/0.51          | ~ (v1_funct_1 @ X12)
% 0.20/0.51          | ~ (v1_relat_1 @ X12))),
% 0.20/0.51      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.20/0.51          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.20/0.51          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.20/0.51              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['28', '29', '30', '36', '37'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.20/0.51          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.20/0.51          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.20/0.51              = (k1_funct_1 @ X0 @ (sk_D_1 @ sk_A @ sk_B)))
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ sk_B)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.51          | ~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.20/0.51              = (k1_funct_1 @ X0 @ (sk_D_1 @ sk_A @ sk_B)))
% 0.20/0.51          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '49'])).
% 0.20/0.51  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('52', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.20/0.51              = (k1_funct_1 @ X0 @ (sk_D_1 @ sk_A @ sk_B)))
% 0.20/0.51          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ sk_B)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.51          | ((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.20/0.51              = (k1_funct_1 @ X0 @ (sk_D_1 @ sk_A @ sk_B)))
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '53'])).
% 0.20/0.51  thf('55', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('56', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) @ sk_A)
% 0.20/0.51            = (k1_funct_1 @ X0 @ (sk_D_1 @ sk_A @ sk_B)))
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      ((((sk_A)
% 0.20/0.51          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.20/0.51        | ((sk_A)
% 0.20/0.51            != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      ((((sk_A)
% 0.20/0.51          != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.20/0.51         <= (~
% 0.20/0.51             (((sk_A)
% 0.20/0.51                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.20/0.51                   sk_A))))),
% 0.20/0.51      inference('split', [status(esa)], ['58'])).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['28', '29', '30', '36', '37'])).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      ((((sk_A)
% 0.20/0.51          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 0.20/0.51         <= (~
% 0.20/0.51             (((sk_A)
% 0.20/0.51                = (k1_funct_1 @ sk_B @ 
% 0.20/0.51                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.20/0.51      inference('split', [status(esa)], ['58'])).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      ((((sk_A) != (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 0.20/0.51         <= (~
% 0.20/0.51             (((sk_A)
% 0.20/0.51                = (k1_funct_1 @ sk_B @ 
% 0.20/0.51                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.51  thf('63', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.51  thf('64', plain,
% 0.20/0.51      ((((sk_A) != (sk_A)))
% 0.20/0.51         <= (~
% 0.20/0.51             (((sk_A)
% 0.20/0.51                = (k1_funct_1 @ sk_B @ 
% 0.20/0.51                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.20/0.51      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.51  thf('65', plain,
% 0.20/0.51      ((((sk_A)
% 0.20/0.51          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['64'])).
% 0.20/0.51  thf('66', plain,
% 0.20/0.51      (~
% 0.20/0.51       (((sk_A)
% 0.20/0.51          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))) | 
% 0.20/0.51       ~
% 0.20/0.51       (((sk_A)
% 0.20/0.51          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.20/0.51      inference('split', [status(esa)], ['58'])).
% 0.20/0.51  thf('67', plain,
% 0.20/0.51      (~
% 0.20/0.51       (((sk_A)
% 0.20/0.51          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['65', '66'])).
% 0.20/0.51  thf('68', plain,
% 0.20/0.51      (((sk_A)
% 0.20/0.51         != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['59', '67'])).
% 0.20/0.51  thf('69', plain,
% 0.20/0.51      ((((sk_A) != (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))
% 0.20/0.51        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['57', '68'])).
% 0.20/0.51  thf('70', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.51  thf('71', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('72', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('73', plain, (((sk_A) != (sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.20/0.51  thf('74', plain, ($false), inference('simplify', [status(thm)], ['73'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

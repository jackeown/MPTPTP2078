%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CvVzfntV2t

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 196 expanded)
%              Number of leaves         :   20 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  876 (2962 expanded)
%              Number of equality atoms :   57 ( 315 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t44_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = A ) )
           => ( B
              = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( ( k2_relat_1 @ A )
                  = ( k1_relat_1 @ B ) )
                & ( ( k5_relat_1 @ A @ B )
                  = A ) )
             => ( B
                = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_funct_1])).

thf('0',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ X14 )
       != X13 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 )
      | ( X14
        = ( k6_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('2',plain,(
    ! [X14: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X14
        = ( k6_relat_1 @ ( k1_relat_1 @ X14 ) ) )
      | ( r2_hidden @ ( sk_C @ X14 @ ( k1_relat_1 @ X14 ) ) @ ( k1_relat_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( X18
       != ( k1_funct_1 @ X17 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( r2_hidden @ ( k4_tarski @ X16 @ ( k1_funct_1 @ X17 @ X16 ) ) @ X17 )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ) @ sk_B )
    | ( sk_B
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','6'])).

thf('8',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ) @ sk_B )
    | ( sk_B
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf('13',plain,(
    sk_B
 != ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_B
 != ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X14: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X14
        = ( k6_relat_1 @ ( k1_relat_1 @ X14 ) ) )
      | ( r2_hidden @ ( sk_C @ X14 @ ( k1_relat_1 @ X14 ) ) @ ( k1_relat_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('19',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) )
    | ( sk_B
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) )
    | ( sk_B
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,(
    sk_B
 != ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('26',plain,(
    r2_hidden @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X12: $i] :
      ( ( ( k9_relat_1 @ X12 @ ( k1_relat_1 @ X12 ) )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X11 @ X9 @ X10 ) @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X2
       != ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X4 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X4 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ X0 ) @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['16','43'])).

thf('45',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ X17 )
      | ( X18
        = ( k1_funct_1 @ X17 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
      = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['31','32'])).

thf('50',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ X17 )
      | ( X18
        = ( k1_funct_1 @ X17 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
    = ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48','54'])).

thf('56',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ X14 )
       != X13 )
      | ( ( k1_funct_1 @ X14 @ ( sk_C @ X14 @ X13 ) )
       != ( sk_C @ X14 @ X13 ) )
      | ( X14
        = ( k6_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('58',plain,(
    ! [X14: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X14
        = ( k6_relat_1 @ ( k1_relat_1 @ X14 ) ) )
      | ( ( k1_funct_1 @ X14 @ ( sk_C @ X14 @ ( k1_relat_1 @ X14 ) ) )
       != ( sk_C @ X14 @ ( k1_relat_1 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
     != ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_B
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
     != ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
    | ( sk_B
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['59','60','61','62','63'])).

thf('65',plain,(
    sk_B
 != ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('66',plain,(
    ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
 != ( sk_C @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CvVzfntV2t
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:04:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 61 iterations in 0.048s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.51  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(t44_funct_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.51           ( ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.21/0.51               ( ( k5_relat_1 @ A @ B ) = ( A ) ) ) =>
% 0.21/0.51             ( ( B ) = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.51              ( ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.21/0.51                  ( ( k5_relat_1 @ A @ B ) = ( A ) ) ) =>
% 0.21/0.51                ( ( B ) = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t44_funct_1])).
% 0.21/0.51  thf('0', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t34_funct_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.51       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.21/0.51         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         (((k1_relat_1 @ X14) != (X13))
% 0.21/0.51          | (r2_hidden @ (sk_C @ X14 @ X13) @ X13)
% 0.21/0.51          | ((X14) = (k6_relat_1 @ X13))
% 0.21/0.51          | ~ (v1_funct_1 @ X14)
% 0.21/0.51          | ~ (v1_relat_1 @ X14))),
% 0.21/0.51      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X14 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X14)
% 0.21/0.51          | ~ (v1_funct_1 @ X14)
% 0.21/0.51          | ((X14) = (k6_relat_1 @ (k1_relat_1 @ X14)))
% 0.21/0.51          | (r2_hidden @ (sk_C @ X14 @ (k1_relat_1 @ X14)) @ (k1_relat_1 @ X14)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.51  thf(t8_funct_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.51       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.21/0.51         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.51           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X16 @ (k1_relat_1 @ X17))
% 0.21/0.51          | ((X18) != (k1_funct_1 @ X17 @ X16))
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X16 @ X18) @ X17)
% 0.21/0.51          | ~ (v1_funct_1 @ X17)
% 0.21/0.51          | ~ (v1_relat_1 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X17)
% 0.21/0.51          | ~ (v1_funct_1 @ X17)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X16 @ (k1_funct_1 @ X17 @ X16)) @ X17)
% 0.21/0.51          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X17)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C @ X0 @ (k1_relat_1 @ X0)) @ 
% 0.21/0.51              (k1_funct_1 @ X0 @ (sk_C @ X0 @ (k1_relat_1 @ X0)))) @ 
% 0.21/0.51             X0)
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '4'])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ 
% 0.21/0.51           (k4_tarski @ (sk_C @ X0 @ (k1_relat_1 @ X0)) @ 
% 0.21/0.51            (k1_funct_1 @ X0 @ (sk_C @ X0 @ (k1_relat_1 @ X0)))) @ 
% 0.21/0.51           X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (((r2_hidden @ 
% 0.21/0.51         (k4_tarski @ (sk_C @ sk_B @ (k2_relat_1 @ sk_A)) @ 
% 0.21/0.51          (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ (k1_relat_1 @ sk_B)))) @ 
% 0.21/0.51         sk_B)
% 0.21/0.51        | ((sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.21/0.51        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.51        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.51      inference('sup+', [status(thm)], ['0', '6'])).
% 0.21/0.51  thf('8', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('9', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('10', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (((r2_hidden @ 
% 0.21/0.51         (k4_tarski @ (sk_C @ sk_B @ (k2_relat_1 @ sk_A)) @ 
% 0.21/0.51          (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ (k2_relat_1 @ sk_A)))) @ 
% 0.21/0.51         sk_B)
% 0.21/0.51        | ((sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.21/0.51  thf('13', plain, (((sk_B) != (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('14', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('15', plain, (((sk_B) != (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      ((r2_hidden @ 
% 0.21/0.51        (k4_tarski @ (sk_C @ sk_B @ (k2_relat_1 @ sk_A)) @ 
% 0.21/0.51         (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ (k2_relat_1 @ sk_A)))) @ 
% 0.21/0.51        sk_B)),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['12', '15'])).
% 0.21/0.51  thf('17', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X14 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X14)
% 0.21/0.51          | ~ (v1_funct_1 @ X14)
% 0.21/0.51          | ((X14) = (k6_relat_1 @ (k1_relat_1 @ X14)))
% 0.21/0.51          | (r2_hidden @ (sk_C @ X14 @ (k1_relat_1 @ X14)) @ (k1_relat_1 @ X14)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (((r2_hidden @ (sk_C @ sk_B @ (k2_relat_1 @ sk_A)) @ (k1_relat_1 @ sk_B))
% 0.21/0.51        | ((sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.21/0.51        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.51        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.51      inference('sup+', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('21', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('22', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (((r2_hidden @ (sk_C @ sk_B @ (k2_relat_1 @ sk_A)) @ (k2_relat_1 @ sk_A))
% 0.21/0.51        | ((sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 0.21/0.51  thf('25', plain, (((sk_B) != (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      ((r2_hidden @ (sk_C @ sk_B @ (k2_relat_1 @ sk_A)) @ (k2_relat_1 @ sk_A))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf(t146_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X12 : $i]:
% 0.21/0.51         (((k9_relat_1 @ X12 @ (k1_relat_1 @ X12)) = (k2_relat_1 @ X12))
% 0.21/0.51          | ~ (v1_relat_1 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.21/0.51  thf(t143_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ C ) =>
% 0.21/0.51       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.21/0.51         ( ?[D:$i]:
% 0.21/0.51           ( ( r2_hidden @ D @ B ) & 
% 0.21/0.51             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.21/0.51             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X11 @ X9 @ X10) @ X10) @ X11)
% 0.21/0.51          | ~ (v1_relat_1 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_D_1 @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r2_hidden @ 
% 0.21/0.51           (k4_tarski @ (sk_D_1 @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.51        | (r2_hidden @ 
% 0.21/0.51           (k4_tarski @ 
% 0.21/0.51            (sk_D_1 @ sk_A @ (k1_relat_1 @ sk_A) @ 
% 0.21/0.51             (sk_C @ sk_B @ (k2_relat_1 @ sk_A))) @ 
% 0.21/0.51            (sk_C @ sk_B @ (k2_relat_1 @ sk_A))) @ 
% 0.21/0.51           sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['26', '30'])).
% 0.21/0.51  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      ((r2_hidden @ 
% 0.21/0.51        (k4_tarski @ 
% 0.21/0.51         (sk_D_1 @ sk_A @ (k1_relat_1 @ sk_A) @ 
% 0.21/0.51          (sk_C @ sk_B @ (k2_relat_1 @ sk_A))) @ 
% 0.21/0.51         (sk_C @ sk_B @ (k2_relat_1 @ sk_A))) @ 
% 0.21/0.51        sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.51  thf('34', plain, (((k5_relat_1 @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d8_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( v1_relat_1 @ B ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( v1_relat_1 @ C ) =>
% 0.21/0.51               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 0.21/0.51                 ( ![D:$i,E:$i]:
% 0.21/0.51                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.21/0.51                     ( ?[F:$i]:
% 0.21/0.51                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 0.21/0.51                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | ((X2) != (k5_relat_1 @ X1 @ X0))
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ X2)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X1)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X5 @ X4) @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X2)
% 0.21/0.51          | ~ (v1_relat_1 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X1)
% 0.21/0.51          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X5 @ X4) @ X0)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X1)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ (k5_relat_1 @ X1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ sk_A)
% 0.21/0.51          | ~ (v1_relat_1 @ sk_B)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k5_relat_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ sk_A)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X2 @ X0) @ sk_B)
% 0.21/0.51          | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['34', '36'])).
% 0.21/0.51  thf('38', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('40', plain, (((k5_relat_1 @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_A)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ sk_A)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X2 @ X0) @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C @ sk_B @ (k2_relat_1 @ sk_A)) @ X0) @ sk_B)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ 
% 0.21/0.51              (sk_D_1 @ sk_A @ (k1_relat_1 @ sk_A) @ 
% 0.21/0.51               (sk_C @ sk_B @ (k2_relat_1 @ sk_A))) @ 
% 0.21/0.51              X0) @ 
% 0.21/0.51             sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['33', '42'])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      ((r2_hidden @ 
% 0.21/0.51        (k4_tarski @ 
% 0.21/0.51         (sk_D_1 @ sk_A @ (k1_relat_1 @ sk_A) @ 
% 0.21/0.51          (sk_C @ sk_B @ (k2_relat_1 @ sk_A))) @ 
% 0.21/0.51         (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ (k2_relat_1 @ sk_A)))) @ 
% 0.21/0.51        sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '43'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ X17)
% 0.21/0.51          | ((X18) = (k1_funct_1 @ X17 @ X16))
% 0.21/0.51          | ~ (v1_funct_1 @ X17)
% 0.21/0.51          | ~ (v1_relat_1 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.51        | ~ (v1_funct_1 @ sk_A)
% 0.21/0.51        | ((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.21/0.51            = (k1_funct_1 @ sk_A @ 
% 0.21/0.51               (sk_D_1 @ sk_A @ (k1_relat_1 @ sk_A) @ 
% 0.21/0.51                (sk_C @ sk_B @ (k2_relat_1 @ sk_A))))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.51  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('48', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      ((r2_hidden @ 
% 0.21/0.51        (k4_tarski @ 
% 0.21/0.51         (sk_D_1 @ sk_A @ (k1_relat_1 @ sk_A) @ 
% 0.21/0.51          (sk_C @ sk_B @ (k2_relat_1 @ sk_A))) @ 
% 0.21/0.51         (sk_C @ sk_B @ (k2_relat_1 @ sk_A))) @ 
% 0.21/0.51        sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ X17)
% 0.21/0.51          | ((X18) = (k1_funct_1 @ X17 @ X16))
% 0.21/0.51          | ~ (v1_funct_1 @ X17)
% 0.21/0.51          | ~ (v1_relat_1 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.51        | ~ (v1_funct_1 @ sk_A)
% 0.21/0.51        | ((sk_C @ sk_B @ (k2_relat_1 @ sk_A))
% 0.21/0.51            = (k1_funct_1 @ sk_A @ 
% 0.21/0.51               (sk_D_1 @ sk_A @ (k1_relat_1 @ sk_A) @ 
% 0.21/0.51                (sk_C @ sk_B @ (k2_relat_1 @ sk_A))))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.51  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('53', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (((sk_C @ sk_B @ (k2_relat_1 @ sk_A))
% 0.21/0.51         = (k1_funct_1 @ sk_A @ 
% 0.21/0.51            (sk_D_1 @ sk_A @ (k1_relat_1 @ sk_A) @ 
% 0.21/0.51             (sk_C @ sk_B @ (k2_relat_1 @ sk_A)))))),
% 0.21/0.51      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.21/0.51         = (sk_C @ sk_B @ (k2_relat_1 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['46', '47', '48', '54'])).
% 0.21/0.51  thf('56', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         (((k1_relat_1 @ X14) != (X13))
% 0.21/0.51          | ((k1_funct_1 @ X14 @ (sk_C @ X14 @ X13)) != (sk_C @ X14 @ X13))
% 0.21/0.51          | ((X14) = (k6_relat_1 @ X13))
% 0.21/0.51          | ~ (v1_funct_1 @ X14)
% 0.21/0.51          | ~ (v1_relat_1 @ X14))),
% 0.21/0.51      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      (![X14 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X14)
% 0.21/0.51          | ~ (v1_funct_1 @ X14)
% 0.21/0.51          | ((X14) = (k6_relat_1 @ (k1_relat_1 @ X14)))
% 0.21/0.51          | ((k1_funct_1 @ X14 @ (sk_C @ X14 @ (k1_relat_1 @ X14)))
% 0.21/0.51              != (sk_C @ X14 @ (k1_relat_1 @ X14))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.21/0.51          != (sk_C @ sk_B @ (k1_relat_1 @ sk_B)))
% 0.21/0.51        | ((sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.21/0.51        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.51        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['56', '58'])).
% 0.21/0.51  thf('60', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('61', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('62', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('63', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.21/0.51          != (sk_C @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.21/0.51        | ((sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['59', '60', '61', '62', '63'])).
% 0.21/0.51  thf('65', plain, (((sk_B) != (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      (((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.21/0.51         != (sk_C @ sk_B @ (k2_relat_1 @ sk_A)))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.21/0.51  thf('67', plain, ($false),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['55', '66'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z5c0ocSOxy

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:16 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 725 expanded)
%              Number of leaves         :   21 ( 255 expanded)
%              Depth                    :   28
%              Number of atoms          : 1671 (7694 expanded)
%              Number of equality atoms :   66 ( 365 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t53_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ? [B: $i] :
            ( ( ( k5_relat_1 @ A @ B )
              = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
            & ( v1_funct_1 @ B )
            & ( v1_relat_1 @ B ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ? [B: $i] :
              ( ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
              & ( v1_funct_1 @ B )
              & ( v1_relat_1 @ B ) )
         => ( v2_funct_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_funct_1])).

thf('0',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('2',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k1_relat_1 @ B ) )
           => ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X16 ) )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('4',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ X1 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('16',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B ) )
      = ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B ) )
    = ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('21',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('22',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('27',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('28',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B ) )
    = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('30',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('42',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('48',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('49',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('51',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['46','47','48','49','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('56',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['34','62'])).

thf('64',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('65',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','67'])).

thf('69',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('70',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('71',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('72',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('77',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','72'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('80',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('81',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('87',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('90',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['88','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('97',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('98',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','72'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['46','47','48','49','50','51'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('104',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['78','105'])).

thf('107',plain,
    ( ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','106'])).

thf('108',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('112',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('117',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X17 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) @ X0 ) )
      | ( ( k2_relat_1 @ X1 )
       != ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) @ X0 ) ) )
      | ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
       != ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B ) )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B ) ) )
    | ( v2_funct_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['110','119'])).

thf('121',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('122',plain,(
    ! [X14: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('123',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B ) )
    = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('127',plain,
    ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('129',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('130',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['127','128','129','130','131'])).

thf('133',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B ) )
    = ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('134',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['120','121','122','123','124','132','133','134'])).

thf('136',plain,(
    v2_funct_1 @ sk_A ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    $false ),
    inference(demod,[status(thm)],['0','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z5c0ocSOxy
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.66/1.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.66/1.86  % Solved by: fo/fo7.sh
% 1.66/1.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.66/1.86  % done 1532 iterations in 1.392s
% 1.66/1.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.66/1.86  % SZS output start Refutation
% 1.66/1.86  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.66/1.86  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.66/1.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.66/1.86  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.66/1.86  thf(sk_A_type, type, sk_A: $i).
% 1.66/1.86  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.66/1.86  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.66/1.86  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.66/1.86  thf(sk_B_type, type, sk_B: $i).
% 1.66/1.86  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.66/1.86  thf(t53_funct_1, conjecture,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.66/1.86       ( ( ?[B:$i]:
% 1.66/1.86           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.66/1.86             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 1.66/1.86         ( v2_funct_1 @ A ) ) ))).
% 1.66/1.86  thf(zf_stmt_0, negated_conjecture,
% 1.66/1.86    (~( ![A:$i]:
% 1.66/1.86        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.66/1.86          ( ( ?[B:$i]:
% 1.66/1.86              ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.66/1.86                ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 1.66/1.86            ( v2_funct_1 @ A ) ) ) )),
% 1.66/1.86    inference('cnf.neg', [status(esa)], [t53_funct_1])).
% 1.66/1.86  thf('0', plain, (~ (v2_funct_1 @ sk_A)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf(fc2_funct_1, axiom,
% 1.66/1.86    (![A:$i,B:$i]:
% 1.66/1.86     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 1.66/1.86         ( v1_funct_1 @ B ) ) =>
% 1.66/1.86       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 1.66/1.86         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 1.66/1.86  thf('1', plain,
% 1.66/1.86      (![X9 : $i, X10 : $i]:
% 1.66/1.86         (~ (v1_funct_1 @ X9)
% 1.66/1.86          | ~ (v1_relat_1 @ X9)
% 1.66/1.86          | ~ (v1_relat_1 @ X10)
% 1.66/1.86          | ~ (v1_funct_1 @ X10)
% 1.66/1.86          | (v1_relat_1 @ (k5_relat_1 @ X9 @ X10)))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc2_funct_1])).
% 1.66/1.86  thf('2', plain,
% 1.66/1.86      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf(t27_funct_1, axiom,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.66/1.86       ( ![B:$i]:
% 1.66/1.86         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.66/1.86           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 1.66/1.86             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 1.66/1.86  thf('3', plain,
% 1.66/1.86      (![X15 : $i, X16 : $i]:
% 1.66/1.86         (~ (v1_relat_1 @ X15)
% 1.66/1.86          | ~ (v1_funct_1 @ X15)
% 1.66/1.86          | (r1_tarski @ (k2_relat_1 @ X15) @ (k1_relat_1 @ X16))
% 1.66/1.86          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X16)) != (k1_relat_1 @ X15))
% 1.66/1.86          | ~ (v1_funct_1 @ X16)
% 1.66/1.86          | ~ (v1_relat_1 @ X16))),
% 1.66/1.86      inference('cnf', [status(esa)], [t27_funct_1])).
% 1.66/1.86  thf('4', plain,
% 1.66/1.86      ((((k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 1.66/1.86          != (k1_relat_1 @ sk_A))
% 1.66/1.86        | ~ (v1_relat_1 @ sk_B)
% 1.66/1.86        | ~ (v1_funct_1 @ sk_B)
% 1.66/1.86        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 1.66/1.86        | ~ (v1_funct_1 @ sk_A)
% 1.66/1.86        | ~ (v1_relat_1 @ sk_A))),
% 1.66/1.86      inference('sup-', [status(thm)], ['2', '3'])).
% 1.66/1.86  thf(t71_relat_1, axiom,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.66/1.86       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.66/1.86  thf('5', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 1.66/1.86      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.66/1.86  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('8', plain, ((v1_funct_1 @ sk_A)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('10', plain,
% 1.66/1.86      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 1.66/1.86        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 1.66/1.86      inference('demod', [status(thm)], ['4', '5', '6', '7', '8', '9'])).
% 1.66/1.86  thf('11', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 1.66/1.86      inference('simplify', [status(thm)], ['10'])).
% 1.66/1.86  thf('12', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 1.66/1.86      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.66/1.86  thf(t46_relat_1, axiom,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ( v1_relat_1 @ A ) =>
% 1.66/1.86       ( ![B:$i]:
% 1.66/1.86         ( ( v1_relat_1 @ B ) =>
% 1.66/1.86           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 1.66/1.86             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 1.66/1.86  thf('13', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (~ (v1_relat_1 @ X0)
% 1.66/1.86          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) = (k1_relat_1 @ X1))
% 1.66/1.86          | ~ (r1_tarski @ (k2_relat_1 @ X1) @ (k1_relat_1 @ X0))
% 1.66/1.86          | ~ (v1_relat_1 @ X1))),
% 1.66/1.86      inference('cnf', [status(esa)], [t46_relat_1])).
% 1.66/1.86  thf('14', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (~ (r1_tarski @ X0 @ (k1_relat_1 @ X1))
% 1.66/1.86          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.66/1.86          | ((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.66/1.86              = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 1.66/1.86          | ~ (v1_relat_1 @ X1))),
% 1.66/1.86      inference('sup-', [status(thm)], ['12', '13'])).
% 1.66/1.86  thf(fc3_funct_1, axiom,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.66/1.86       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.66/1.86  thf('15', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('16', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 1.66/1.86      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.66/1.86  thf('17', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (~ (r1_tarski @ X0 @ (k1_relat_1 @ X1))
% 1.66/1.86          | ((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X0))
% 1.66/1.86          | ~ (v1_relat_1 @ X1))),
% 1.66/1.86      inference('demod', [status(thm)], ['14', '15', '16'])).
% 1.66/1.86  thf('18', plain,
% 1.66/1.86      ((~ (v1_relat_1 @ sk_B)
% 1.66/1.86        | ((k1_relat_1 @ 
% 1.66/1.86            (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B))
% 1.66/1.86            = (k2_relat_1 @ sk_A)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['11', '17'])).
% 1.66/1.86  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('20', plain,
% 1.66/1.86      (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B))
% 1.66/1.86         = (k2_relat_1 @ sk_A))),
% 1.66/1.86      inference('demod', [status(thm)], ['18', '19'])).
% 1.66/1.86  thf(t78_relat_1, axiom,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ( v1_relat_1 @ A ) =>
% 1.66/1.86       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 1.66/1.86  thf('21', plain,
% 1.66/1.86      (![X7 : $i]:
% 1.66/1.86         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X7)) @ X7) = (X7))
% 1.66/1.86          | ~ (v1_relat_1 @ X7))),
% 1.66/1.86      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.66/1.86  thf('22', plain,
% 1.66/1.86      ((((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ 
% 1.66/1.86          (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B))
% 1.66/1.86          = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B))
% 1.66/1.86        | ~ (v1_relat_1 @ 
% 1.66/1.86             (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B)))),
% 1.66/1.86      inference('sup+', [status(thm)], ['20', '21'])).
% 1.66/1.86  thf('23', plain,
% 1.66/1.86      ((~ (v1_funct_1 @ sk_B)
% 1.66/1.86        | ~ (v1_relat_1 @ sk_B)
% 1.66/1.86        | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 1.66/1.86        | ~ (v1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 1.66/1.86        | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ 
% 1.66/1.86            (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B))
% 1.66/1.86            = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['1', '22'])).
% 1.66/1.86  thf('24', plain, ((v1_funct_1 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('26', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('27', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('28', plain,
% 1.66/1.86      (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ 
% 1.66/1.86         (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B))
% 1.66/1.86         = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B))),
% 1.66/1.86      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 1.66/1.86  thf('29', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 1.66/1.86      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.66/1.86  thf('30', plain,
% 1.66/1.86      (![X7 : $i]:
% 1.66/1.86         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X7)) @ X7) = (X7))
% 1.66/1.86          | ~ (v1_relat_1 @ X7))),
% 1.66/1.86      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.66/1.86  thf('31', plain,
% 1.66/1.86      (![X0 : $i]:
% 1.66/1.86         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.66/1.86            = (k6_relat_1 @ X0))
% 1.66/1.86          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.66/1.86      inference('sup+', [status(thm)], ['29', '30'])).
% 1.66/1.86  thf('32', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('33', plain,
% 1.66/1.86      (![X0 : $i]:
% 1.66/1.86         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.66/1.86           = (k6_relat_1 @ X0))),
% 1.66/1.86      inference('demod', [status(thm)], ['31', '32'])).
% 1.66/1.86  thf('34', plain,
% 1.66/1.86      (![X9 : $i, X10 : $i]:
% 1.66/1.86         (~ (v1_funct_1 @ X9)
% 1.66/1.86          | ~ (v1_relat_1 @ X9)
% 1.66/1.86          | ~ (v1_relat_1 @ X10)
% 1.66/1.86          | ~ (v1_funct_1 @ X10)
% 1.66/1.86          | (v1_relat_1 @ (k5_relat_1 @ X9 @ X10)))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc2_funct_1])).
% 1.66/1.86  thf('35', plain,
% 1.66/1.86      (![X0 : $i]:
% 1.66/1.86         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.66/1.86           = (k6_relat_1 @ X0))),
% 1.66/1.86      inference('demod', [status(thm)], ['31', '32'])).
% 1.66/1.86  thf(t55_relat_1, axiom,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ( v1_relat_1 @ A ) =>
% 1.66/1.86       ( ![B:$i]:
% 1.66/1.86         ( ( v1_relat_1 @ B ) =>
% 1.66/1.86           ( ![C:$i]:
% 1.66/1.86             ( ( v1_relat_1 @ C ) =>
% 1.66/1.86               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.66/1.86                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.66/1.86  thf('36', plain,
% 1.66/1.86      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.66/1.86         (~ (v1_relat_1 @ X2)
% 1.66/1.86          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 1.66/1.86              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 1.66/1.86          | ~ (v1_relat_1 @ X4)
% 1.66/1.86          | ~ (v1_relat_1 @ X3))),
% 1.66/1.86      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.66/1.86  thf('37', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.66/1.86            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.66/1.86               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 1.66/1.86          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.66/1.86          | ~ (v1_relat_1 @ X1)
% 1.66/1.86          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.66/1.86      inference('sup+', [status(thm)], ['35', '36'])).
% 1.66/1.86  thf('38', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('39', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('40', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.66/1.86            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.66/1.86               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 1.66/1.86          | ~ (v1_relat_1 @ X1))),
% 1.66/1.86      inference('demod', [status(thm)], ['37', '38', '39'])).
% 1.66/1.86  thf('41', plain,
% 1.66/1.86      (![X0 : $i]:
% 1.66/1.86         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.66/1.86           = (k6_relat_1 @ X0))),
% 1.66/1.86      inference('demod', [status(thm)], ['31', '32'])).
% 1.66/1.86  thf('42', plain,
% 1.66/1.86      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.66/1.86         (~ (v1_relat_1 @ X2)
% 1.66/1.86          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 1.66/1.86              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 1.66/1.86          | ~ (v1_relat_1 @ X4)
% 1.66/1.86          | ~ (v1_relat_1 @ X3))),
% 1.66/1.86      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.66/1.86  thf('43', plain,
% 1.66/1.86      (![X9 : $i, X10 : $i]:
% 1.66/1.86         (~ (v1_funct_1 @ X9)
% 1.66/1.86          | ~ (v1_relat_1 @ X9)
% 1.66/1.86          | ~ (v1_relat_1 @ X10)
% 1.66/1.86          | ~ (v1_funct_1 @ X10)
% 1.66/1.86          | (v1_funct_1 @ (k5_relat_1 @ X9 @ X10)))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc2_funct_1])).
% 1.66/1.86  thf('44', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.86         ((v1_funct_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 1.66/1.86          | ~ (v1_relat_1 @ X2)
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X1)
% 1.66/1.86          | ~ (v1_funct_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 1.66/1.86          | ~ (v1_funct_1 @ (k5_relat_1 @ X2 @ X1)))),
% 1.66/1.86      inference('sup+', [status(thm)], ['42', '43'])).
% 1.66/1.86  thf('45', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.86         (~ (v1_funct_1 @ (k5_relat_1 @ X2 @ X1))
% 1.66/1.86          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 1.66/1.86          | ~ (v1_funct_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X1)
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X2)
% 1.66/1.86          | (v1_funct_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 1.66/1.86      inference('simplify', [status(thm)], ['44'])).
% 1.66/1.86  thf('46', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.66/1.86          | (v1_funct_1 @ 
% 1.66/1.86             (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.66/1.86              (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 1.66/1.86          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.66/1.86          | ~ (v1_relat_1 @ X1)
% 1.66/1.86          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.66/1.86          | ~ (v1_funct_1 @ X1)
% 1.66/1.86          | ~ (v1_funct_1 @ 
% 1.66/1.86               (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['41', '45'])).
% 1.66/1.86  thf('47', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('48', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('49', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('50', plain,
% 1.66/1.86      (![X0 : $i]:
% 1.66/1.86         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.66/1.86           = (k6_relat_1 @ X0))),
% 1.66/1.86      inference('demod', [status(thm)], ['31', '32'])).
% 1.66/1.86  thf('51', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('52', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         ((v1_funct_1 @ 
% 1.66/1.86           (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.66/1.86            (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 1.66/1.86          | ~ (v1_relat_1 @ X1)
% 1.66/1.86          | ~ (v1_funct_1 @ X1))),
% 1.66/1.86      inference('demod', [status(thm)], ['46', '47', '48', '49', '50', '51'])).
% 1.66/1.86  thf('53', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         ((v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_funct_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X0))),
% 1.66/1.86      inference('sup+', [status(thm)], ['40', '52'])).
% 1.66/1.86  thf('54', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (~ (v1_funct_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | (v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.66/1.86      inference('simplify', [status(thm)], ['53'])).
% 1.66/1.86  thf('55', plain,
% 1.66/1.86      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.66/1.86         (~ (v1_relat_1 @ X2)
% 1.66/1.86          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 1.66/1.86              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 1.66/1.86          | ~ (v1_relat_1 @ X4)
% 1.66/1.86          | ~ (v1_relat_1 @ X3))),
% 1.66/1.86      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.66/1.86  thf('56', plain,
% 1.66/1.86      (![X9 : $i, X10 : $i]:
% 1.66/1.86         (~ (v1_funct_1 @ X9)
% 1.66/1.86          | ~ (v1_relat_1 @ X9)
% 1.66/1.86          | ~ (v1_relat_1 @ X10)
% 1.66/1.86          | ~ (v1_funct_1 @ X10)
% 1.66/1.86          | (v1_relat_1 @ (k5_relat_1 @ X9 @ X10)))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc2_funct_1])).
% 1.66/1.86  thf('57', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.86         ((v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 1.66/1.86          | ~ (v1_relat_1 @ X2)
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X1)
% 1.66/1.86          | ~ (v1_funct_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 1.66/1.86          | ~ (v1_funct_1 @ (k5_relat_1 @ X2 @ X1)))),
% 1.66/1.86      inference('sup+', [status(thm)], ['55', '56'])).
% 1.66/1.86  thf('58', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.86         (~ (v1_funct_1 @ (k5_relat_1 @ X2 @ X1))
% 1.66/1.86          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 1.66/1.86          | ~ (v1_funct_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X1)
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X2)
% 1.66/1.86          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 1.66/1.86      inference('simplify', [status(thm)], ['57'])).
% 1.66/1.86  thf('59', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.86         (~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_funct_1 @ X0)
% 1.66/1.86          | (v1_relat_1 @ 
% 1.66/1.86             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 1.66/1.86          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.66/1.86          | ~ (v1_relat_1 @ X2)
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_funct_1 @ X2)
% 1.66/1.86          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['54', '58'])).
% 1.66/1.86  thf('60', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('61', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.86         (~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_funct_1 @ X0)
% 1.66/1.86          | (v1_relat_1 @ 
% 1.66/1.86             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 1.66/1.86          | ~ (v1_relat_1 @ X2)
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_funct_1 @ X2)
% 1.66/1.86          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.66/1.86      inference('demod', [status(thm)], ['59', '60'])).
% 1.66/1.86  thf('62', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.86         (~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.66/1.86          | ~ (v1_funct_1 @ X2)
% 1.66/1.86          | ~ (v1_relat_1 @ X2)
% 1.66/1.86          | (v1_relat_1 @ 
% 1.66/1.86             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 1.66/1.86          | ~ (v1_funct_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X0))),
% 1.66/1.86      inference('simplify', [status(thm)], ['61'])).
% 1.66/1.86  thf('63', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.86         (~ (v1_funct_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.66/1.86          | ~ (v1_funct_1 @ (k6_relat_1 @ X1))
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_funct_1 @ X0)
% 1.66/1.86          | (v1_relat_1 @ 
% 1.66/1.86             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 1.66/1.86          | ~ (v1_relat_1 @ X2)
% 1.66/1.86          | ~ (v1_funct_1 @ X2))),
% 1.66/1.86      inference('sup-', [status(thm)], ['34', '62'])).
% 1.66/1.86  thf('64', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('65', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('66', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.86         (~ (v1_funct_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_funct_1 @ X0)
% 1.66/1.86          | (v1_relat_1 @ 
% 1.66/1.86             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 1.66/1.86          | ~ (v1_relat_1 @ X2)
% 1.66/1.86          | ~ (v1_funct_1 @ X2))),
% 1.66/1.86      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.66/1.86  thf('67', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.86         (~ (v1_funct_1 @ X2)
% 1.66/1.86          | ~ (v1_relat_1 @ X2)
% 1.66/1.86          | (v1_relat_1 @ 
% 1.66/1.86             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_funct_1 @ X0))),
% 1.66/1.86      inference('simplify', [status(thm)], ['66'])).
% 1.66/1.86  thf('68', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 1.66/1.86          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 1.66/1.86          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.66/1.86          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.66/1.86          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 1.66/1.86      inference('sup+', [status(thm)], ['33', '67'])).
% 1.66/1.86  thf('69', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('70', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('71', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('72', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('73', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 1.66/1.86      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 1.66/1.86  thf('74', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.86         (~ (v1_funct_1 @ (k5_relat_1 @ X2 @ X1))
% 1.66/1.86          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 1.66/1.86          | ~ (v1_funct_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X1)
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X2)
% 1.66/1.86          | (v1_funct_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 1.66/1.86      inference('simplify', [status(thm)], ['44'])).
% 1.66/1.86  thf('75', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.86         ((v1_funct_1 @ 
% 1.66/1.86           (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 1.66/1.86            (k5_relat_1 @ (k6_relat_1 @ X0) @ X2)))
% 1.66/1.86          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.66/1.86          | ~ (v1_relat_1 @ X2)
% 1.66/1.86          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.66/1.86          | ~ (v1_funct_1 @ X2)
% 1.66/1.86          | ~ (v1_funct_1 @ 
% 1.66/1.86               (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['73', '74'])).
% 1.66/1.86  thf('76', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('77', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('78', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.86         ((v1_funct_1 @ 
% 1.66/1.86           (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 1.66/1.86            (k5_relat_1 @ (k6_relat_1 @ X0) @ X2)))
% 1.66/1.86          | ~ (v1_relat_1 @ X2)
% 1.66/1.86          | ~ (v1_funct_1 @ X2)
% 1.66/1.86          | ~ (v1_funct_1 @ 
% 1.66/1.86               (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))),
% 1.66/1.86      inference('demod', [status(thm)], ['75', '76', '77'])).
% 1.66/1.86  thf('79', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 1.66/1.86      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 1.66/1.86  thf(t80_relat_1, axiom,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ( v1_relat_1 @ A ) =>
% 1.66/1.86       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.66/1.86  thf('80', plain,
% 1.66/1.86      (![X8 : $i]:
% 1.66/1.86         (((k5_relat_1 @ X8 @ (k6_relat_1 @ (k2_relat_1 @ X8))) = (X8))
% 1.66/1.86          | ~ (v1_relat_1 @ X8))),
% 1.66/1.86      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.66/1.86  thf('81', plain,
% 1.66/1.86      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.66/1.86         (~ (v1_relat_1 @ X2)
% 1.66/1.86          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 1.66/1.86              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 1.66/1.86          | ~ (v1_relat_1 @ X4)
% 1.66/1.86          | ~ (v1_relat_1 @ X3))),
% 1.66/1.86      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.66/1.86  thf('82', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (((k5_relat_1 @ X1 @ X0)
% 1.66/1.86            = (k5_relat_1 @ X1 @ 
% 1.66/1.86               (k5_relat_1 @ X0 @ 
% 1.66/1.86                (k6_relat_1 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))))
% 1.66/1.86          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.66/1.86          | ~ (v1_relat_1 @ X1)
% 1.66/1.86          | ~ (v1_relat_1 @ 
% 1.66/1.86               (k6_relat_1 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 1.66/1.86          | ~ (v1_relat_1 @ X0))),
% 1.66/1.86      inference('sup+', [status(thm)], ['80', '81'])).
% 1.66/1.86  thf('83', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('84', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (((k5_relat_1 @ X1 @ X0)
% 1.66/1.86            = (k5_relat_1 @ X1 @ 
% 1.66/1.86               (k5_relat_1 @ X0 @ 
% 1.66/1.86                (k6_relat_1 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))))
% 1.66/1.86          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.66/1.86          | ~ (v1_relat_1 @ X1)
% 1.66/1.86          | ~ (v1_relat_1 @ X0))),
% 1.66/1.86      inference('demod', [status(thm)], ['82', '83'])).
% 1.66/1.86  thf('85', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.66/1.86          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.66/1.86          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 1.66/1.86              = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 1.66/1.86                 (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.66/1.86                  (k6_relat_1 @ 
% 1.66/1.86                   (k2_relat_1 @ 
% 1.66/1.86                    (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['79', '84'])).
% 1.66/1.86  thf('86', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('87', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('88', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 1.66/1.86           = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 1.66/1.86              (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.66/1.86               (k6_relat_1 @ 
% 1.66/1.86                (k2_relat_1 @ 
% 1.66/1.86                 (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))))))),
% 1.66/1.86      inference('demod', [status(thm)], ['85', '86', '87'])).
% 1.66/1.86  thf('89', plain,
% 1.66/1.86      (![X7 : $i]:
% 1.66/1.86         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X7)) @ X7) = (X7))
% 1.66/1.86          | ~ (v1_relat_1 @ X7))),
% 1.66/1.86      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.66/1.86  thf('90', plain,
% 1.66/1.86      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.66/1.86         (~ (v1_relat_1 @ X2)
% 1.66/1.86          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 1.66/1.86              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 1.66/1.86          | ~ (v1_relat_1 @ X4)
% 1.66/1.86          | ~ (v1_relat_1 @ X3))),
% 1.66/1.86      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.66/1.86  thf('91', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (((k5_relat_1 @ X0 @ X1)
% 1.66/1.86            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.66/1.86               (k5_relat_1 @ X0 @ X1)))
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.66/1.86          | ~ (v1_relat_1 @ X1)
% 1.66/1.86          | ~ (v1_relat_1 @ X0))),
% 1.66/1.86      inference('sup+', [status(thm)], ['89', '90'])).
% 1.66/1.86  thf('92', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('93', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (((k5_relat_1 @ X0 @ X1)
% 1.66/1.86            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.66/1.86               (k5_relat_1 @ X0 @ X1)))
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X1)
% 1.66/1.86          | ~ (v1_relat_1 @ X0))),
% 1.66/1.86      inference('demod', [status(thm)], ['91', '92'])).
% 1.66/1.86  thf('94', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (~ (v1_relat_1 @ X1)
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ((k5_relat_1 @ X0 @ X1)
% 1.66/1.86              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.66/1.86                 (k5_relat_1 @ X0 @ X1))))),
% 1.66/1.86      inference('simplify', [status(thm)], ['93'])).
% 1.66/1.86  thf('95', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (((k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 1.66/1.86            (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.66/1.86             (k6_relat_1 @ 
% 1.66/1.86              (k2_relat_1 @ 
% 1.66/1.86               (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))))
% 1.66/1.86            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X1))) @ 
% 1.66/1.86               (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))
% 1.66/1.86          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.66/1.86          | ~ (v1_relat_1 @ 
% 1.66/1.86               (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.66/1.86                (k6_relat_1 @ 
% 1.66/1.86                 (k2_relat_1 @ 
% 1.66/1.86                  (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))))))),
% 1.66/1.86      inference('sup+', [status(thm)], ['88', '94'])).
% 1.66/1.86  thf('96', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 1.66/1.86           = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 1.66/1.86              (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.66/1.86               (k6_relat_1 @ 
% 1.66/1.86                (k2_relat_1 @ 
% 1.66/1.86                 (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))))))),
% 1.66/1.86      inference('demod', [status(thm)], ['85', '86', '87'])).
% 1.66/1.86  thf('97', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 1.66/1.86      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.66/1.86  thf('98', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('99', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 1.66/1.86      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 1.66/1.86  thf('100', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 1.66/1.86           = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 1.66/1.86              (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))))),
% 1.66/1.86      inference('demod', [status(thm)], ['95', '96', '97', '98', '99'])).
% 1.66/1.86  thf('101', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         ((v1_funct_1 @ 
% 1.66/1.86           (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.66/1.86            (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 1.66/1.86          | ~ (v1_relat_1 @ X1)
% 1.66/1.86          | ~ (v1_funct_1 @ X1))),
% 1.66/1.86      inference('demod', [status(thm)], ['46', '47', '48', '49', '50', '51'])).
% 1.66/1.86  thf('102', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         ((v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 1.66/1.86          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 1.66/1.86          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.66/1.86      inference('sup+', [status(thm)], ['100', '101'])).
% 1.66/1.86  thf('103', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('104', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('105', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 1.66/1.86      inference('demod', [status(thm)], ['102', '103', '104'])).
% 1.66/1.86  thf('106', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.86         ((v1_funct_1 @ 
% 1.66/1.86           (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 1.66/1.86            (k5_relat_1 @ (k6_relat_1 @ X0) @ X2)))
% 1.66/1.86          | ~ (v1_relat_1 @ X2)
% 1.66/1.86          | ~ (v1_funct_1 @ X2))),
% 1.66/1.86      inference('demod', [status(thm)], ['78', '105'])).
% 1.66/1.86  thf('107', plain,
% 1.66/1.86      (((v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B))
% 1.66/1.86        | ~ (v1_funct_1 @ sk_B)
% 1.66/1.86        | ~ (v1_relat_1 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['28', '106'])).
% 1.66/1.86  thf('108', plain, ((v1_funct_1 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('109', plain, ((v1_relat_1 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('110', plain,
% 1.66/1.86      ((v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B))),
% 1.66/1.86      inference('demod', [status(thm)], ['107', '108', '109'])).
% 1.66/1.86  thf('111', plain,
% 1.66/1.86      (![X8 : $i]:
% 1.66/1.86         (((k5_relat_1 @ X8 @ (k6_relat_1 @ (k2_relat_1 @ X8))) = (X8))
% 1.66/1.86          | ~ (v1_relat_1 @ X8))),
% 1.66/1.86      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.66/1.86  thf('112', plain,
% 1.66/1.86      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.66/1.86         (~ (v1_relat_1 @ X2)
% 1.66/1.86          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 1.66/1.86              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 1.66/1.86          | ~ (v1_relat_1 @ X4)
% 1.66/1.86          | ~ (v1_relat_1 @ X3))),
% 1.66/1.86      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.66/1.86  thf('113', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (((k5_relat_1 @ X0 @ X1)
% 1.66/1.86            = (k5_relat_1 @ X0 @ 
% 1.66/1.86               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X1)
% 1.66/1.86          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 1.66/1.86      inference('sup+', [status(thm)], ['111', '112'])).
% 1.66/1.86  thf('114', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('115', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (((k5_relat_1 @ X0 @ X1)
% 1.66/1.86            = (k5_relat_1 @ X0 @ 
% 1.66/1.86               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X1))),
% 1.66/1.86      inference('demod', [status(thm)], ['113', '114'])).
% 1.66/1.86  thf('116', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (~ (v1_relat_1 @ X1)
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ((k5_relat_1 @ X0 @ X1)
% 1.66/1.86              = (k5_relat_1 @ X0 @ 
% 1.66/1.86                 (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1))))),
% 1.66/1.86      inference('simplify', [status(thm)], ['115'])).
% 1.66/1.86  thf(t48_funct_1, axiom,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.66/1.86       ( ![B:$i]:
% 1.66/1.86         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.66/1.86           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.66/1.86               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 1.66/1.86             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 1.66/1.86  thf('117', plain,
% 1.66/1.86      (![X17 : $i, X18 : $i]:
% 1.66/1.86         (~ (v1_relat_1 @ X17)
% 1.66/1.86          | ~ (v1_funct_1 @ X17)
% 1.66/1.86          | (v2_funct_1 @ X17)
% 1.66/1.86          | ((k2_relat_1 @ X17) != (k1_relat_1 @ X18))
% 1.66/1.86          | ~ (v2_funct_1 @ (k5_relat_1 @ X17 @ X18))
% 1.66/1.86          | ~ (v1_funct_1 @ X18)
% 1.66/1.86          | ~ (v1_relat_1 @ X18))),
% 1.66/1.86      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.66/1.86  thf('118', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (~ (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 1.66/1.86          | ~ (v1_relat_1 @ X1)
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ 
% 1.66/1.86               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X1)) @ X0))
% 1.66/1.86          | ~ (v1_funct_1 @ 
% 1.66/1.86               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X1)) @ X0))
% 1.66/1.86          | ((k2_relat_1 @ X1)
% 1.66/1.86              != (k1_relat_1 @ 
% 1.66/1.86                  (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X1)) @ X0)))
% 1.66/1.86          | (v2_funct_1 @ X1)
% 1.66/1.86          | ~ (v1_funct_1 @ X1)
% 1.66/1.86          | ~ (v1_relat_1 @ X1))),
% 1.66/1.86      inference('sup-', [status(thm)], ['116', '117'])).
% 1.66/1.86  thf('119', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (~ (v1_funct_1 @ X1)
% 1.66/1.86          | (v2_funct_1 @ X1)
% 1.66/1.86          | ((k2_relat_1 @ X1)
% 1.66/1.86              != (k1_relat_1 @ 
% 1.66/1.86                  (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X1)) @ X0)))
% 1.66/1.86          | ~ (v1_funct_1 @ 
% 1.66/1.86               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X1)) @ X0))
% 1.66/1.86          | ~ (v1_relat_1 @ 
% 1.66/1.86               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X1)) @ X0))
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_relat_1 @ X1)
% 1.66/1.86          | ~ (v2_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 1.66/1.86      inference('simplify', [status(thm)], ['118'])).
% 1.66/1.86  thf('120', plain,
% 1.66/1.86      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 1.66/1.86        | ~ (v1_relat_1 @ sk_A)
% 1.66/1.86        | ~ (v1_relat_1 @ sk_B)
% 1.66/1.86        | ~ (v1_relat_1 @ 
% 1.66/1.86             (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B))
% 1.66/1.86        | ((k2_relat_1 @ sk_A)
% 1.66/1.86            != (k1_relat_1 @ 
% 1.66/1.86                (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B)))
% 1.66/1.86        | (v2_funct_1 @ sk_A)
% 1.66/1.86        | ~ (v1_funct_1 @ sk_A))),
% 1.66/1.86      inference('sup-', [status(thm)], ['110', '119'])).
% 1.66/1.86  thf('121', plain,
% 1.66/1.86      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf(fc4_funct_1, axiom,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.66/1.86       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.66/1.86  thf('122', plain, (![X14 : $i]: (v2_funct_1 @ (k6_relat_1 @ X14))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.66/1.86  thf('123', plain, ((v1_relat_1 @ sk_A)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('124', plain, ((v1_relat_1 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('125', plain,
% 1.66/1.86      (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ 
% 1.66/1.86         (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B))
% 1.66/1.86         = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B))),
% 1.66/1.86      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 1.66/1.86  thf('126', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.86         (~ (v1_funct_1 @ X2)
% 1.66/1.86          | ~ (v1_relat_1 @ X2)
% 1.66/1.86          | (v1_relat_1 @ 
% 1.66/1.86             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 1.66/1.86          | ~ (v1_relat_1 @ X0)
% 1.66/1.86          | ~ (v1_funct_1 @ X0))),
% 1.66/1.86      inference('simplify', [status(thm)], ['66'])).
% 1.66/1.86  thf('127', plain,
% 1.66/1.86      (((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B))
% 1.66/1.86        | ~ (v1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 1.66/1.86        | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 1.66/1.86        | ~ (v1_relat_1 @ sk_B)
% 1.66/1.86        | ~ (v1_funct_1 @ sk_B))),
% 1.66/1.86      inference('sup+', [status(thm)], ['125', '126'])).
% 1.66/1.86  thf('128', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('129', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.66/1.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.66/1.86  thf('130', plain, ((v1_relat_1 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('131', plain, ((v1_funct_1 @ sk_B)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('132', plain,
% 1.66/1.86      ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B))),
% 1.66/1.86      inference('demod', [status(thm)], ['127', '128', '129', '130', '131'])).
% 1.66/1.86  thf('133', plain,
% 1.66/1.86      (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B))
% 1.66/1.86         = (k2_relat_1 @ sk_A))),
% 1.66/1.86      inference('demod', [status(thm)], ['18', '19'])).
% 1.66/1.86  thf('134', plain, ((v1_funct_1 @ sk_A)),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('135', plain,
% 1.66/1.86      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A)) | (v2_funct_1 @ sk_A))),
% 1.66/1.86      inference('demod', [status(thm)],
% 1.66/1.86                ['120', '121', '122', '123', '124', '132', '133', '134'])).
% 1.66/1.86  thf('136', plain, ((v2_funct_1 @ sk_A)),
% 1.66/1.86      inference('simplify', [status(thm)], ['135'])).
% 1.66/1.86  thf('137', plain, ($false), inference('demod', [status(thm)], ['0', '136'])).
% 1.66/1.86  
% 1.66/1.86  % SZS output end Refutation
% 1.66/1.86  
% 1.66/1.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

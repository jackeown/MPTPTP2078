%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L1Yo6WOLeF

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:42 EST 2020

% Result     : Theorem 17.28s
% Output     : Refutation 17.28s
% Verified   : 
% Statistics : Number of formulae       :  253 (6619 expanded)
%              Number of leaves         :   23 (2014 expanded)
%              Depth                    :   41
%              Number of atoms          : 2323 (100869 expanded)
%              Number of equality atoms :  152 (10080 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) @ X10 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(t64_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( v2_funct_1 @ A )
                & ( ( k2_relat_1 @ B )
                  = ( k1_relat_1 @ A ) )
                & ( ( k5_relat_1 @ B @ A )
                  = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
             => ( B
                = ( k2_funct_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_1])).

thf('1',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) @ X10 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('3',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ sk_A )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ X17 @ ( k2_funct_1 @ X17 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('8',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k2_relat_1 @ X2 ) )
        = ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('10',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k10_relat_1 @ X4 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('12',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
      = ( k10_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('13',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('14',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('18',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','20'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k5_relat_1 @ X6 @ ( k5_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_A ) )
      = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','26'])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('29',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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

thf('30',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('31',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) @ X10 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_A ) )
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['28','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_A ) )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k2_funct_1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','39','40','41','42','43'])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_funct_1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['6','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k5_relat_1 @ X6 @ ( k5_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('54',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ X17 @ ( k2_funct_1 @ X17 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['52','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51','64'])).

thf('66',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A )
      = ( k5_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['5','65'])).

thf('67',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','20'])).

thf('68',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k5_relat_1 @ X6 @ ( k5_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('74',plain,
    ( ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('76',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('81',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) @ X10 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('82',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('83',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ X17 @ ( k2_funct_1 @ X17 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('84',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('85',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k5_relat_1 @ X6 @ ( k5_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['83','90'])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('94',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('95',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) @ X10 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('102',plain,
    ( ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92','97','98','99','100','101'])).

thf('103',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k5_relat_1 @ X6 @ ( k5_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ sk_A )
      = ( k5_relat_1 @ sk_A @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['82','107'])).

thf('109',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('110',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('111',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( sk_A
    = ( k5_relat_1 @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['108','109','110','111','112','113','114'])).

thf('116',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k5_relat_1 @ X6 @ ( k5_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('117',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k10_relat_1 @ X4 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 ) ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['115','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( sk_A
    = ( k5_relat_1 @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['108','109','110','111','112','113','114'])).

thf('123',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('126',plain,
    ( ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('131',plain,(
    v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 ) ) )
        = ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','131'])).

thf('133',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
      = ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['81','132'])).

thf('134',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('135',plain,(
    ! [X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k2_relat_1 @ X2 ) )
        = ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('136',plain,
    ( ( ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
      = ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['133','139','140','141'])).

thf('143',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) @ X10 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('144',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
      = ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','144'])).

thf('146',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51','64'])).

thf('150',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('153',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k5_relat_1 @ X6 @ ( k5_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('155',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['152','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
    ( ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['151','158'])).

thf('160',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('162',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['159','160','161','162'])).

thf('164',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['150','163'])).

thf('165',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
      = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['79','164'])).

thf('166',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
    = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) @ X10 )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('170',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['133','139','140','141'])).

thf(t44_funct_1,axiom,(
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

thf('171',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X14
        = ( k6_relat_1 @ ( k1_relat_1 @ X14 ) ) )
      | ( ( k5_relat_1 @ X15 @ X14 )
       != X15 )
      | ( ( k2_relat_1 @ X15 )
       != ( k1_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_funct_1])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k5_relat_1 @ sk_A @ sk_B ) )
       != X0 )
      | ( ( k5_relat_1 @ sk_A @ sk_B )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['133','139','140','141'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k5_relat_1 @ sk_A @ sk_B ) )
       != X0 )
      | ( ( k5_relat_1 @ sk_A @ sk_B )
        = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('176',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('178',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k5_relat_1 @ X6 @ ( k5_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('179',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('180',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['177','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['176','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,
    ( ( v1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['175','185'])).

thf('187',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('190',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('192',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('193',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ X17 @ ( k2_funct_1 @ X17 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('194',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['192','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['191','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,
    ( ( v1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['190','200'])).

thf('202',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['201','202','203','204'])).

thf('206',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['186','187','188','189','205','206','207'])).

thf('209',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['159','160','161','162'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k5_relat_1 @ sk_A @ sk_B ) )
       != X0 )
      | ( ( k5_relat_1 @ sk_A @ sk_B )
        = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['174','208','209'])).

thf('211',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
     != sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ sk_A @ sk_B )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['169','210'])).

thf('212',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
     != sk_B )
    | ( ( k5_relat_1 @ sk_A @ sk_B )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['211','212','213','214'])).

thf('216',plain,
    ( ( ( k5_relat_1 @ sk_A @ sk_B )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
     != sk_B ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,
    ( ( sk_B != sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ sk_A @ sk_B )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['168','216'])).

thf('218',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_A @ sk_B )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['217','218'])).

thf('220',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
    = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['167','220'])).

thf('222',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('223',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['221','222'])).

thf('224',plain,
    ( ( sk_B
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','223'])).

thf('225',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( sk_B
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['224','225'])).

thf('227',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['226','227'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L1Yo6WOLeF
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:38:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 17.28/17.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 17.28/17.47  % Solved by: fo/fo7.sh
% 17.28/17.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.28/17.47  % done 8139 iterations in 17.007s
% 17.28/17.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 17.28/17.47  % SZS output start Refutation
% 17.28/17.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 17.28/17.47  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 17.28/17.47  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 17.28/17.47  thf(sk_A_type, type, sk_A: $i).
% 17.28/17.47  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 17.28/17.47  thf(sk_B_type, type, sk_B: $i).
% 17.28/17.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 17.28/17.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 17.28/17.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 17.28/17.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 17.28/17.47  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 17.28/17.47  thf(t78_relat_1, axiom,
% 17.28/17.47    (![A:$i]:
% 17.28/17.47     ( ( v1_relat_1 @ A ) =>
% 17.28/17.47       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 17.28/17.47  thf('0', plain,
% 17.28/17.47      (![X10 : $i]:
% 17.28/17.47         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X10)) @ X10) = (X10))
% 17.28/17.47          | ~ (v1_relat_1 @ X10))),
% 17.28/17.47      inference('cnf', [status(esa)], [t78_relat_1])).
% 17.28/17.47  thf(t64_funct_1, conjecture,
% 17.28/17.47    (![A:$i]:
% 17.28/17.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 17.28/17.47       ( ![B:$i]:
% 17.28/17.47         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 17.28/17.47           ( ( ( v2_funct_1 @ A ) & 
% 17.28/17.47               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 17.28/17.47               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 17.28/17.47             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 17.28/17.47  thf(zf_stmt_0, negated_conjecture,
% 17.28/17.47    (~( ![A:$i]:
% 17.28/17.47        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 17.28/17.47          ( ![B:$i]:
% 17.28/17.47            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 17.28/17.47              ( ( ( v2_funct_1 @ A ) & 
% 17.28/17.47                  ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 17.28/17.47                  ( ( k5_relat_1 @ B @ A ) =
% 17.28/17.47                    ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 17.28/17.47                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 17.28/17.47    inference('cnf.neg', [status(esa)], [t64_funct_1])).
% 17.28/17.47  thf('1', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('2', plain,
% 17.28/17.47      (![X10 : $i]:
% 17.28/17.47         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X10)) @ X10) = (X10))
% 17.28/17.47          | ~ (v1_relat_1 @ X10))),
% 17.28/17.47      inference('cnf', [status(esa)], [t78_relat_1])).
% 17.28/17.47  thf('3', plain,
% 17.28/17.47      ((((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ sk_A) = (sk_A))
% 17.28/17.47        | ~ (v1_relat_1 @ sk_A))),
% 17.28/17.47      inference('sup+', [status(thm)], ['1', '2'])).
% 17.28/17.47  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('5', plain,
% 17.28/17.47      (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ sk_A) = (sk_A))),
% 17.28/17.47      inference('demod', [status(thm)], ['3', '4'])).
% 17.28/17.47  thf(dt_k2_funct_1, axiom,
% 17.28/17.47    (![A:$i]:
% 17.28/17.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 17.28/17.47       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 17.28/17.47         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 17.28/17.47  thf('6', plain,
% 17.28/17.47      (![X11 : $i]:
% 17.28/17.47         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 17.28/17.47          | ~ (v1_funct_1 @ X11)
% 17.28/17.47          | ~ (v1_relat_1 @ X11))),
% 17.28/17.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 17.28/17.47  thf(t61_funct_1, axiom,
% 17.28/17.47    (![A:$i]:
% 17.28/17.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 17.28/17.47       ( ( v2_funct_1 @ A ) =>
% 17.28/17.47         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 17.28/17.47             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 17.28/17.47           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 17.28/17.47             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 17.28/17.47  thf('7', plain,
% 17.28/17.47      (![X17 : $i]:
% 17.28/17.47         (~ (v2_funct_1 @ X17)
% 17.28/17.47          | ((k5_relat_1 @ X17 @ (k2_funct_1 @ X17))
% 17.28/17.47              = (k6_relat_1 @ (k1_relat_1 @ X17)))
% 17.28/17.47          | ~ (v1_funct_1 @ X17)
% 17.28/17.47          | ~ (v1_relat_1 @ X17))),
% 17.28/17.47      inference('cnf', [status(esa)], [t61_funct_1])).
% 17.28/17.47  thf('8', plain,
% 17.28/17.47      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf(t169_relat_1, axiom,
% 17.28/17.47    (![A:$i]:
% 17.28/17.47     ( ( v1_relat_1 @ A ) =>
% 17.28/17.47       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 17.28/17.47  thf('9', plain,
% 17.28/17.47      (![X2 : $i]:
% 17.28/17.47         (((k10_relat_1 @ X2 @ (k2_relat_1 @ X2)) = (k1_relat_1 @ X2))
% 17.28/17.47          | ~ (v1_relat_1 @ X2))),
% 17.28/17.47      inference('cnf', [status(esa)], [t169_relat_1])).
% 17.28/17.47  thf('10', plain,
% 17.28/17.47      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf(t182_relat_1, axiom,
% 17.28/17.47    (![A:$i]:
% 17.28/17.47     ( ( v1_relat_1 @ A ) =>
% 17.28/17.47       ( ![B:$i]:
% 17.28/17.47         ( ( v1_relat_1 @ B ) =>
% 17.28/17.47           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 17.28/17.47             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 17.28/17.47  thf('11', plain,
% 17.28/17.47      (![X3 : $i, X4 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X3)
% 17.28/17.47          | ((k1_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 17.28/17.47              = (k10_relat_1 @ X4 @ (k1_relat_1 @ X3)))
% 17.28/17.47          | ~ (v1_relat_1 @ X4))),
% 17.28/17.47      inference('cnf', [status(esa)], [t182_relat_1])).
% 17.28/17.47  thf('12', plain,
% 17.28/17.47      ((((k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 17.28/17.47          = (k10_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))
% 17.28/17.47        | ~ (v1_relat_1 @ sk_B)
% 17.28/17.47        | ~ (v1_relat_1 @ sk_A))),
% 17.28/17.47      inference('sup+', [status(thm)], ['10', '11'])).
% 17.28/17.47  thf(t71_relat_1, axiom,
% 17.28/17.47    (![A:$i]:
% 17.28/17.47     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 17.28/17.47       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 17.28/17.47  thf('13', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 17.28/17.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 17.28/17.47  thf('14', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('16', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('17', plain,
% 17.28/17.47      (((k2_relat_1 @ sk_A) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 17.28/17.47      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 17.28/17.47  thf('18', plain,
% 17.28/17.47      ((((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B)) | ~ (v1_relat_1 @ sk_B))),
% 17.28/17.47      inference('sup+', [status(thm)], ['9', '17'])).
% 17.28/17.47  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('20', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 17.28/17.47      inference('demod', [status(thm)], ['18', '19'])).
% 17.28/17.47  thf('21', plain,
% 17.28/17.47      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 17.28/17.47      inference('demod', [status(thm)], ['8', '20'])).
% 17.28/17.47  thf(t55_relat_1, axiom,
% 17.28/17.47    (![A:$i]:
% 17.28/17.47     ( ( v1_relat_1 @ A ) =>
% 17.28/17.47       ( ![B:$i]:
% 17.28/17.47         ( ( v1_relat_1 @ B ) =>
% 17.28/17.47           ( ![C:$i]:
% 17.28/17.47             ( ( v1_relat_1 @ C ) =>
% 17.28/17.47               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 17.28/17.47                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 17.28/17.47  thf('22', plain,
% 17.28/17.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X5)
% 17.28/17.47          | ((k5_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 17.28/17.47              = (k5_relat_1 @ X6 @ (k5_relat_1 @ X5 @ X7)))
% 17.28/17.47          | ~ (v1_relat_1 @ X7)
% 17.28/17.47          | ~ (v1_relat_1 @ X6))),
% 17.28/17.47      inference('cnf', [status(esa)], [t55_relat_1])).
% 17.28/17.47  thf('23', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 17.28/17.47            = (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ sk_B)
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ sk_A))),
% 17.28/17.47      inference('sup+', [status(thm)], ['21', '22'])).
% 17.28/17.47  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('26', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 17.28/17.47            = (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ X0))),
% 17.28/17.47      inference('demod', [status(thm)], ['23', '24', '25'])).
% 17.28/17.47  thf('27', plain,
% 17.28/17.47      ((((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ (k2_funct_1 @ sk_A))
% 17.28/17.47          = (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 17.28/17.47        | ~ (v1_relat_1 @ sk_A)
% 17.28/17.47        | ~ (v1_funct_1 @ sk_A)
% 17.28/17.47        | ~ (v2_funct_1 @ sk_A)
% 17.28/17.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 17.28/17.47      inference('sup+', [status(thm)], ['7', '26'])).
% 17.28/17.47  thf('28', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 17.28/17.47      inference('demod', [status(thm)], ['18', '19'])).
% 17.28/17.47  thf('29', plain,
% 17.28/17.47      (![X11 : $i]:
% 17.28/17.47         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 17.28/17.47          | ~ (v1_funct_1 @ X11)
% 17.28/17.47          | ~ (v1_relat_1 @ X11))),
% 17.28/17.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 17.28/17.47  thf(t55_funct_1, axiom,
% 17.28/17.47    (![A:$i]:
% 17.28/17.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 17.28/17.47       ( ( v2_funct_1 @ A ) =>
% 17.28/17.47         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 17.28/17.47           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 17.28/17.47  thf('30', plain,
% 17.28/17.47      (![X16 : $i]:
% 17.28/17.47         (~ (v2_funct_1 @ X16)
% 17.28/17.47          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 17.28/17.47          | ~ (v1_funct_1 @ X16)
% 17.28/17.47          | ~ (v1_relat_1 @ X16))),
% 17.28/17.47      inference('cnf', [status(esa)], [t55_funct_1])).
% 17.28/17.47  thf('31', plain,
% 17.28/17.47      (![X10 : $i]:
% 17.28/17.47         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X10)) @ X10) = (X10))
% 17.28/17.47          | ~ (v1_relat_1 @ X10))),
% 17.28/17.47      inference('cnf', [status(esa)], [t78_relat_1])).
% 17.28/17.47  thf('32', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 17.28/17.47            = (k2_funct_1 @ X0))
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | ~ (v2_funct_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 17.28/17.47      inference('sup+', [status(thm)], ['30', '31'])).
% 17.28/17.47  thf('33', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | ~ (v2_funct_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 17.28/17.47              = (k2_funct_1 @ X0)))),
% 17.28/17.47      inference('sup-', [status(thm)], ['29', '32'])).
% 17.28/17.47  thf('34', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 17.28/17.47            = (k2_funct_1 @ X0))
% 17.28/17.47          | ~ (v2_funct_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X0))),
% 17.28/17.47      inference('simplify', [status(thm)], ['33'])).
% 17.28/17.47  thf('35', plain,
% 17.28/17.47      ((((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ (k2_funct_1 @ sk_A))
% 17.28/17.47          = (k2_funct_1 @ sk_A))
% 17.28/17.47        | ~ (v1_relat_1 @ sk_A)
% 17.28/17.47        | ~ (v1_funct_1 @ sk_A)
% 17.28/17.47        | ~ (v2_funct_1 @ sk_A))),
% 17.28/17.47      inference('sup+', [status(thm)], ['28', '34'])).
% 17.28/17.47  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('37', plain, ((v1_funct_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('38', plain, ((v2_funct_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('39', plain,
% 17.28/17.47      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ (k2_funct_1 @ sk_A))
% 17.28/17.47         = (k2_funct_1 @ sk_A))),
% 17.28/17.47      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 17.28/17.47  thf('40', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('42', plain, ((v1_funct_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('43', plain, ((v2_funct_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('44', plain,
% 17.28/17.47      ((((k2_funct_1 @ sk_A)
% 17.28/17.47          = (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))
% 17.28/17.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 17.28/17.47      inference('demod', [status(thm)], ['27', '39', '40', '41', '42', '43'])).
% 17.28/17.47  thf('45', plain,
% 17.28/17.47      ((~ (v1_relat_1 @ sk_A)
% 17.28/17.47        | ~ (v1_funct_1 @ sk_A)
% 17.28/17.47        | ((k2_funct_1 @ sk_A)
% 17.28/17.47            = (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))))),
% 17.28/17.47      inference('sup-', [status(thm)], ['6', '44'])).
% 17.28/17.47  thf('46', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('47', plain, ((v1_funct_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('48', plain,
% 17.28/17.47      (((k2_funct_1 @ sk_A)
% 17.28/17.47         = (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 17.28/17.47      inference('demod', [status(thm)], ['45', '46', '47'])).
% 17.28/17.47  thf('49', plain,
% 17.28/17.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X5)
% 17.28/17.47          | ((k5_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 17.28/17.47              = (k5_relat_1 @ X6 @ (k5_relat_1 @ X5 @ X7)))
% 17.28/17.47          | ~ (v1_relat_1 @ X7)
% 17.28/17.47          | ~ (v1_relat_1 @ X6))),
% 17.28/17.47      inference('cnf', [status(esa)], [t55_relat_1])).
% 17.28/17.47  thf('50', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ X0)
% 17.28/17.47            = (k5_relat_1 @ sk_B @ 
% 17.28/17.47               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ sk_B)
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 17.28/17.47      inference('sup+', [status(thm)], ['48', '49'])).
% 17.28/17.47  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('52', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('53', plain,
% 17.28/17.47      (![X11 : $i]:
% 17.28/17.47         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 17.28/17.47          | ~ (v1_funct_1 @ X11)
% 17.28/17.47          | ~ (v1_relat_1 @ X11))),
% 17.28/17.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 17.28/17.47  thf('54', plain,
% 17.28/17.47      (![X17 : $i]:
% 17.28/17.47         (~ (v2_funct_1 @ X17)
% 17.28/17.47          | ((k5_relat_1 @ X17 @ (k2_funct_1 @ X17))
% 17.28/17.47              = (k6_relat_1 @ (k1_relat_1 @ X17)))
% 17.28/17.47          | ~ (v1_funct_1 @ X17)
% 17.28/17.47          | ~ (v1_relat_1 @ X17))),
% 17.28/17.47      inference('cnf', [status(esa)], [t61_funct_1])).
% 17.28/17.47  thf(dt_k5_relat_1, axiom,
% 17.28/17.47    (![A:$i,B:$i]:
% 17.28/17.47     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 17.28/17.47       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 17.28/17.47  thf('55', plain,
% 17.28/17.47      (![X0 : $i, X1 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 17.28/17.47      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 17.28/17.47  thf('56', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         ((v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | ~ (v2_funct_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 17.28/17.47          | ~ (v1_relat_1 @ X0))),
% 17.28/17.47      inference('sup+', [status(thm)], ['54', '55'])).
% 17.28/17.47  thf('57', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 17.28/17.47          | ~ (v2_funct_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 17.28/17.47      inference('simplify', [status(thm)], ['56'])).
% 17.28/17.47  thf('58', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | ~ (v2_funct_1 @ X0))),
% 17.28/17.47      inference('sup-', [status(thm)], ['53', '57'])).
% 17.28/17.47  thf('59', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (~ (v2_funct_1 @ X0)
% 17.28/17.47          | (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X0))),
% 17.28/17.47      inference('simplify', [status(thm)], ['58'])).
% 17.28/17.47  thf('60', plain,
% 17.28/17.47      (((v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 17.28/17.47        | ~ (v1_relat_1 @ sk_A)
% 17.28/17.47        | ~ (v1_funct_1 @ sk_A)
% 17.28/17.47        | ~ (v2_funct_1 @ sk_A))),
% 17.28/17.47      inference('sup+', [status(thm)], ['52', '59'])).
% 17.28/17.47  thf('61', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('62', plain, ((v1_funct_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('63', plain, ((v2_funct_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('64', plain, ((v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 17.28/17.47      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 17.28/17.47  thf('65', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ X0)
% 17.28/17.47            = (k5_relat_1 @ sk_B @ 
% 17.28/17.47               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ X0))),
% 17.28/17.47      inference('demod', [status(thm)], ['50', '51', '64'])).
% 17.28/17.47  thf('66', plain,
% 17.28/17.47      ((((k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A) = (k5_relat_1 @ sk_B @ sk_A))
% 17.28/17.47        | ~ (v1_relat_1 @ sk_A))),
% 17.28/17.47      inference('sup+', [status(thm)], ['5', '65'])).
% 17.28/17.47  thf('67', plain,
% 17.28/17.47      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 17.28/17.47      inference('demod', [status(thm)], ['8', '20'])).
% 17.28/17.47  thf('68', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('69', plain,
% 17.28/17.47      (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A)
% 17.28/17.47         = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 17.28/17.47      inference('demod', [status(thm)], ['66', '67', '68'])).
% 17.28/17.47  thf('70', plain,
% 17.28/17.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X5)
% 17.28/17.47          | ((k5_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 17.28/17.47              = (k5_relat_1 @ X6 @ (k5_relat_1 @ X5 @ X7)))
% 17.28/17.47          | ~ (v1_relat_1 @ X7)
% 17.28/17.47          | ~ (v1_relat_1 @ X6))),
% 17.28/17.47      inference('cnf', [status(esa)], [t55_relat_1])).
% 17.28/17.47  thf('71', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 17.28/17.47            = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ sk_A))),
% 17.28/17.47      inference('sup+', [status(thm)], ['69', '70'])).
% 17.28/17.47  thf('72', plain,
% 17.28/17.47      (((k2_funct_1 @ sk_A)
% 17.28/17.47         = (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 17.28/17.47      inference('demod', [status(thm)], ['45', '46', '47'])).
% 17.28/17.47  thf('73', plain,
% 17.28/17.47      (![X0 : $i, X1 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 17.28/17.47      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 17.28/17.47  thf('74', plain,
% 17.28/17.47      (((v1_relat_1 @ (k2_funct_1 @ sk_A))
% 17.28/17.47        | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 17.28/17.47        | ~ (v1_relat_1 @ sk_B))),
% 17.28/17.47      inference('sup+', [status(thm)], ['72', '73'])).
% 17.28/17.47  thf('75', plain, ((v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 17.28/17.47      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 17.28/17.47  thf('76', plain, ((v1_relat_1 @ sk_B)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('77', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_A))),
% 17.28/17.47      inference('demod', [status(thm)], ['74', '75', '76'])).
% 17.28/17.47  thf('78', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('79', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 17.28/17.47            = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ X0))),
% 17.28/17.47      inference('demod', [status(thm)], ['71', '77', '78'])).
% 17.28/17.47  thf('80', plain,
% 17.28/17.47      (![X0 : $i, X1 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 17.28/17.47      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 17.28/17.47  thf('81', plain,
% 17.28/17.47      (![X10 : $i]:
% 17.28/17.47         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X10)) @ X10) = (X10))
% 17.28/17.47          | ~ (v1_relat_1 @ X10))),
% 17.28/17.47      inference('cnf', [status(esa)], [t78_relat_1])).
% 17.28/17.47  thf('82', plain,
% 17.28/17.47      (![X17 : $i]:
% 17.28/17.47         (~ (v2_funct_1 @ X17)
% 17.28/17.47          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 17.28/17.47              = (k6_relat_1 @ (k2_relat_1 @ X17)))
% 17.28/17.47          | ~ (v1_funct_1 @ X17)
% 17.28/17.47          | ~ (v1_relat_1 @ X17))),
% 17.28/17.47      inference('cnf', [status(esa)], [t61_funct_1])).
% 17.28/17.47  thf('83', plain,
% 17.28/17.47      (![X17 : $i]:
% 17.28/17.47         (~ (v2_funct_1 @ X17)
% 17.28/17.47          | ((k5_relat_1 @ X17 @ (k2_funct_1 @ X17))
% 17.28/17.47              = (k6_relat_1 @ (k1_relat_1 @ X17)))
% 17.28/17.47          | ~ (v1_funct_1 @ X17)
% 17.28/17.47          | ~ (v1_relat_1 @ X17))),
% 17.28/17.47      inference('cnf', [status(esa)], [t61_funct_1])).
% 17.28/17.47  thf('84', plain,
% 17.28/17.47      (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ sk_A) = (sk_A))),
% 17.28/17.47      inference('demod', [status(thm)], ['3', '4'])).
% 17.28/17.47  thf('85', plain,
% 17.28/17.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X5)
% 17.28/17.47          | ((k5_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 17.28/17.47              = (k5_relat_1 @ X6 @ (k5_relat_1 @ X5 @ X7)))
% 17.28/17.47          | ~ (v1_relat_1 @ X7)
% 17.28/17.47          | ~ (v1_relat_1 @ X6))),
% 17.28/17.47      inference('cnf', [status(esa)], [t55_relat_1])).
% 17.28/17.47  thf('86', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (((k5_relat_1 @ sk_A @ X0)
% 17.28/17.47            = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 17.28/17.47               (k5_relat_1 @ sk_A @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ sk_A))),
% 17.28/17.47      inference('sup+', [status(thm)], ['84', '85'])).
% 17.28/17.47  thf('87', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('88', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (((k5_relat_1 @ sk_A @ X0)
% 17.28/17.47            = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 17.28/17.47               (k5_relat_1 @ sk_A @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 17.28/17.47          | ~ (v1_relat_1 @ X0))),
% 17.28/17.47      inference('demod', [status(thm)], ['86', '87'])).
% 17.28/17.47  thf('89', plain, ((v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 17.28/17.47      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 17.28/17.47  thf('90', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (((k5_relat_1 @ sk_A @ X0)
% 17.28/17.47            = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 17.28/17.47               (k5_relat_1 @ sk_A @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ X0))),
% 17.28/17.47      inference('demod', [status(thm)], ['88', '89'])).
% 17.28/17.47  thf('91', plain,
% 17.28/17.47      ((((k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A))
% 17.28/17.47          = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 17.28/17.47             (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 17.28/17.47        | ~ (v1_relat_1 @ sk_A)
% 17.28/17.47        | ~ (v1_funct_1 @ sk_A)
% 17.28/17.47        | ~ (v2_funct_1 @ sk_A)
% 17.28/17.47        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 17.28/17.47      inference('sup+', [status(thm)], ['83', '90'])).
% 17.28/17.47  thf('92', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('93', plain, ((v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 17.28/17.47      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 17.28/17.47  thf('94', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 17.28/17.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 17.28/17.47  thf('95', plain,
% 17.28/17.47      (![X10 : $i]:
% 17.28/17.47         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X10)) @ X10) = (X10))
% 17.28/17.47          | ~ (v1_relat_1 @ X10))),
% 17.28/17.47      inference('cnf', [status(esa)], [t78_relat_1])).
% 17.28/17.47  thf('96', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 17.28/17.47            = (k6_relat_1 @ X0))
% 17.28/17.47          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 17.28/17.47      inference('sup+', [status(thm)], ['94', '95'])).
% 17.28/17.47  thf('97', plain,
% 17.28/17.47      (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 17.28/17.47         (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 17.28/17.47         = (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 17.28/17.47      inference('sup-', [status(thm)], ['93', '96'])).
% 17.28/17.47  thf('98', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('99', plain, ((v1_funct_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('100', plain, ((v2_funct_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('101', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_A))),
% 17.28/17.47      inference('demod', [status(thm)], ['74', '75', '76'])).
% 17.28/17.47  thf('102', plain,
% 17.28/17.47      (((k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A))
% 17.28/17.47         = (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 17.28/17.47      inference('demod', [status(thm)],
% 17.28/17.47                ['91', '92', '97', '98', '99', '100', '101'])).
% 17.28/17.47  thf('103', plain,
% 17.28/17.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X5)
% 17.28/17.47          | ((k5_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 17.28/17.47              = (k5_relat_1 @ X6 @ (k5_relat_1 @ X5 @ X7)))
% 17.28/17.47          | ~ (v1_relat_1 @ X7)
% 17.28/17.47          | ~ (v1_relat_1 @ X6))),
% 17.28/17.47      inference('cnf', [status(esa)], [t55_relat_1])).
% 17.28/17.47  thf('104', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ X0)
% 17.28/17.47            = (k5_relat_1 @ sk_A @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ sk_A)
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 17.28/17.47      inference('sup+', [status(thm)], ['102', '103'])).
% 17.28/17.47  thf('105', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('106', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_A))),
% 17.28/17.47      inference('demod', [status(thm)], ['74', '75', '76'])).
% 17.28/17.47  thf('107', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ X0)
% 17.28/17.47            = (k5_relat_1 @ sk_A @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ X0))),
% 17.28/17.47      inference('demod', [status(thm)], ['104', '105', '106'])).
% 17.28/17.47  thf('108', plain,
% 17.28/17.47      ((((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ sk_A)
% 17.28/17.47          = (k5_relat_1 @ sk_A @ (k6_relat_1 @ (k2_relat_1 @ sk_A))))
% 17.28/17.47        | ~ (v1_relat_1 @ sk_A)
% 17.28/17.47        | ~ (v1_funct_1 @ sk_A)
% 17.28/17.47        | ~ (v2_funct_1 @ sk_A)
% 17.28/17.47        | ~ (v1_relat_1 @ sk_A))),
% 17.28/17.47      inference('sup+', [status(thm)], ['82', '107'])).
% 17.28/17.47  thf('109', plain,
% 17.28/17.47      (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ sk_A) = (sk_A))),
% 17.28/17.47      inference('demod', [status(thm)], ['3', '4'])).
% 17.28/17.47  thf('110', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 17.28/17.47      inference('demod', [status(thm)], ['18', '19'])).
% 17.28/17.47  thf('111', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('112', plain, ((v1_funct_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('113', plain, ((v2_funct_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('114', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('115', plain,
% 17.28/17.47      (((sk_A) = (k5_relat_1 @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B))))),
% 17.28/17.47      inference('demod', [status(thm)],
% 17.28/17.47                ['108', '109', '110', '111', '112', '113', '114'])).
% 17.28/17.47  thf('116', plain,
% 17.28/17.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X5)
% 17.28/17.47          | ((k5_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 17.28/17.47              = (k5_relat_1 @ X6 @ (k5_relat_1 @ X5 @ X7)))
% 17.28/17.47          | ~ (v1_relat_1 @ X7)
% 17.28/17.47          | ~ (v1_relat_1 @ X6))),
% 17.28/17.47      inference('cnf', [status(esa)], [t55_relat_1])).
% 17.28/17.47  thf('117', plain,
% 17.28/17.47      (![X3 : $i, X4 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X3)
% 17.28/17.47          | ((k1_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 17.28/17.47              = (k10_relat_1 @ X4 @ (k1_relat_1 @ X3)))
% 17.28/17.47          | ~ (v1_relat_1 @ X4))),
% 17.28/17.47      inference('cnf', [status(esa)], [t182_relat_1])).
% 17.28/17.47  thf('118', plain,
% 17.28/17.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.28/17.47         (((k1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 17.28/17.47            = (k10_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k1_relat_1 @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ X2)
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 17.28/17.47          | ~ (v1_relat_1 @ X0))),
% 17.28/17.47      inference('sup+', [status(thm)], ['116', '117'])).
% 17.28/17.47  thf('119', plain,
% 17.28/17.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X2)
% 17.28/17.47          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 17.28/17.47              = (k10_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k1_relat_1 @ X0))))),
% 17.28/17.47      inference('simplify', [status(thm)], ['118'])).
% 17.28/17.47  thf('120', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ sk_A)
% 17.28/17.47          | ((k1_relat_1 @ 
% 17.28/17.47              (k5_relat_1 @ sk_A @ 
% 17.28/17.47               (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)))
% 17.28/17.47              = (k10_relat_1 @ 
% 17.28/17.47                 (k5_relat_1 @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B))) @ 
% 17.28/17.47                 (k1_relat_1 @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ sk_A)
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B))))),
% 17.28/17.47      inference('sup-', [status(thm)], ['115', '119'])).
% 17.28/17.47  thf('121', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('122', plain,
% 17.28/17.47      (((sk_A) = (k5_relat_1 @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B))))),
% 17.28/17.47      inference('demod', [status(thm)],
% 17.28/17.47                ['108', '109', '110', '111', '112', '113', '114'])).
% 17.28/17.47  thf('123', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('124', plain,
% 17.28/17.47      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('125', plain,
% 17.28/17.47      (![X0 : $i, X1 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 17.28/17.47      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 17.28/17.47  thf('126', plain,
% 17.28/17.47      (((v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 17.28/17.47        | ~ (v1_relat_1 @ sk_A)
% 17.28/17.47        | ~ (v1_relat_1 @ sk_B))),
% 17.28/17.47      inference('sup+', [status(thm)], ['124', '125'])).
% 17.28/17.47  thf('127', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('128', plain, ((v1_relat_1 @ sk_B)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('129', plain, ((v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 17.28/17.47      inference('demod', [status(thm)], ['126', '127', '128'])).
% 17.28/17.47  thf('130', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 17.28/17.47      inference('demod', [status(thm)], ['18', '19'])).
% 17.28/17.47  thf('131', plain, ((v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 17.28/17.47      inference('demod', [status(thm)], ['129', '130'])).
% 17.28/17.47  thf('132', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (((k1_relat_1 @ 
% 17.28/17.47            (k5_relat_1 @ sk_A @ 
% 17.28/17.47             (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)))
% 17.28/17.47            = (k10_relat_1 @ sk_A @ (k1_relat_1 @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ X0))),
% 17.28/17.47      inference('demod', [status(thm)], ['120', '121', '122', '123', '131'])).
% 17.28/17.47  thf('133', plain,
% 17.28/17.47      ((((k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 17.28/17.47          = (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 17.28/17.47        | ~ (v1_relat_1 @ sk_B)
% 17.28/17.47        | ~ (v1_relat_1 @ sk_B))),
% 17.28/17.47      inference('sup+', [status(thm)], ['81', '132'])).
% 17.28/17.47  thf('134', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 17.28/17.47      inference('demod', [status(thm)], ['18', '19'])).
% 17.28/17.47  thf('135', plain,
% 17.28/17.47      (![X2 : $i]:
% 17.28/17.47         (((k10_relat_1 @ X2 @ (k2_relat_1 @ X2)) = (k1_relat_1 @ X2))
% 17.28/17.47          | ~ (v1_relat_1 @ X2))),
% 17.28/17.47      inference('cnf', [status(esa)], [t169_relat_1])).
% 17.28/17.47  thf('136', plain,
% 17.28/17.47      ((((k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_relat_1 @ sk_A))
% 17.28/17.47        | ~ (v1_relat_1 @ sk_A))),
% 17.28/17.47      inference('sup+', [status(thm)], ['134', '135'])).
% 17.28/17.47  thf('137', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('138', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('139', plain,
% 17.28/17.47      (((k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 17.28/17.47      inference('demod', [status(thm)], ['136', '137', '138'])).
% 17.28/17.47  thf('140', plain, ((v1_relat_1 @ sk_B)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('141', plain, ((v1_relat_1 @ sk_B)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('142', plain,
% 17.28/17.47      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) = (k2_relat_1 @ sk_B))),
% 17.28/17.47      inference('demod', [status(thm)], ['133', '139', '140', '141'])).
% 17.28/17.47  thf('143', plain,
% 17.28/17.47      (![X10 : $i]:
% 17.28/17.47         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X10)) @ X10) = (X10))
% 17.28/17.47          | ~ (v1_relat_1 @ X10))),
% 17.28/17.47      inference('cnf', [status(esa)], [t78_relat_1])).
% 17.28/17.47  thf('144', plain,
% 17.28/17.47      ((((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 17.28/17.47          (k5_relat_1 @ sk_A @ sk_B)) = (k5_relat_1 @ sk_A @ sk_B))
% 17.28/17.47        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 17.28/17.47      inference('sup+', [status(thm)], ['142', '143'])).
% 17.28/17.47  thf('145', plain,
% 17.28/17.47      ((~ (v1_relat_1 @ sk_B)
% 17.28/17.47        | ~ (v1_relat_1 @ sk_A)
% 17.28/17.47        | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 17.28/17.47            (k5_relat_1 @ sk_A @ sk_B)) = (k5_relat_1 @ sk_A @ sk_B)))),
% 17.28/17.47      inference('sup-', [status(thm)], ['80', '144'])).
% 17.28/17.47  thf('146', plain, ((v1_relat_1 @ sk_B)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('147', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('148', plain,
% 17.28/17.47      (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 17.28/17.47         (k5_relat_1 @ sk_A @ sk_B)) = (k5_relat_1 @ sk_A @ sk_B))),
% 17.28/17.47      inference('demod', [status(thm)], ['145', '146', '147'])).
% 17.28/17.47  thf('149', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ X0)
% 17.28/17.47            = (k5_relat_1 @ sk_B @ 
% 17.28/17.47               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ X0))),
% 17.28/17.47      inference('demod', [status(thm)], ['50', '51', '64'])).
% 17.28/17.47  thf('150', plain,
% 17.28/17.47      ((((k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B))
% 17.28/17.47          = (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ sk_B)))
% 17.28/17.47        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 17.28/17.47      inference('sup+', [status(thm)], ['148', '149'])).
% 17.28/17.47  thf('151', plain,
% 17.28/17.47      (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 17.28/17.47         (k5_relat_1 @ sk_A @ sk_B)) = (k5_relat_1 @ sk_A @ sk_B))),
% 17.28/17.47      inference('demod', [status(thm)], ['145', '146', '147'])).
% 17.28/17.47  thf('152', plain,
% 17.28/17.47      (![X0 : $i, X1 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 17.28/17.47      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 17.28/17.47  thf('153', plain,
% 17.28/17.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X5)
% 17.28/17.47          | ((k5_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 17.28/17.47              = (k5_relat_1 @ X6 @ (k5_relat_1 @ X5 @ X7)))
% 17.28/17.47          | ~ (v1_relat_1 @ X7)
% 17.28/17.47          | ~ (v1_relat_1 @ X6))),
% 17.28/17.47      inference('cnf', [status(esa)], [t55_relat_1])).
% 17.28/17.47  thf('154', plain,
% 17.28/17.47      (![X0 : $i, X1 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 17.28/17.47      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 17.28/17.47  thf('155', plain,
% 17.28/17.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.28/17.47         ((v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ X2)
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 17.28/17.47      inference('sup+', [status(thm)], ['153', '154'])).
% 17.28/17.47  thf('156', plain,
% 17.28/17.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X2)
% 17.28/17.47          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 17.28/17.47      inference('simplify', [status(thm)], ['155'])).
% 17.28/17.47  thf('157', plain,
% 17.28/17.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | ~ (v1_relat_1 @ X2)
% 17.28/17.47          | ~ (v1_relat_1 @ X0))),
% 17.28/17.47      inference('sup-', [status(thm)], ['152', '156'])).
% 17.28/17.47  thf('158', plain,
% 17.28/17.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X2)
% 17.28/17.47          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | ~ (v1_relat_1 @ X0))),
% 17.28/17.47      inference('simplify', [status(thm)], ['157'])).
% 17.28/17.47  thf('159', plain,
% 17.28/17.47      (((v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 17.28/17.47        | ~ (v1_relat_1 @ sk_A)
% 17.28/17.47        | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 17.28/17.47        | ~ (v1_relat_1 @ sk_B))),
% 17.28/17.47      inference('sup+', [status(thm)], ['151', '158'])).
% 17.28/17.47  thf('160', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('161', plain, ((v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 17.28/17.47      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 17.28/17.47  thf('162', plain, ((v1_relat_1 @ sk_B)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('163', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))),
% 17.28/17.47      inference('demod', [status(thm)], ['159', '160', '161', '162'])).
% 17.28/17.47  thf('164', plain,
% 17.28/17.47      (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B))
% 17.28/17.47         = (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ sk_B)))),
% 17.28/17.47      inference('demod', [status(thm)], ['150', '163'])).
% 17.28/17.47  thf('165', plain,
% 17.28/17.47      ((((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B)
% 17.28/17.47          = (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ sk_B)))
% 17.28/17.47        | ~ (v1_relat_1 @ sk_B))),
% 17.28/17.47      inference('sup+', [status(thm)], ['79', '164'])).
% 17.28/17.47  thf('166', plain, ((v1_relat_1 @ sk_B)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('167', plain,
% 17.28/17.47      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B)
% 17.28/17.47         = (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ sk_B)))),
% 17.28/17.47      inference('demod', [status(thm)], ['165', '166'])).
% 17.28/17.47  thf('168', plain,
% 17.28/17.47      (![X10 : $i]:
% 17.28/17.47         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X10)) @ X10) = (X10))
% 17.28/17.47          | ~ (v1_relat_1 @ X10))),
% 17.28/17.47      inference('cnf', [status(esa)], [t78_relat_1])).
% 17.28/17.47  thf('169', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 17.28/17.47            = (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ X0))),
% 17.28/17.47      inference('demod', [status(thm)], ['23', '24', '25'])).
% 17.28/17.47  thf('170', plain,
% 17.28/17.47      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) = (k2_relat_1 @ sk_B))),
% 17.28/17.47      inference('demod', [status(thm)], ['133', '139', '140', '141'])).
% 17.28/17.47  thf(t44_funct_1, axiom,
% 17.28/17.47    (![A:$i]:
% 17.28/17.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 17.28/17.47       ( ![B:$i]:
% 17.28/17.47         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 17.28/17.47           ( ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 17.28/17.47               ( ( k5_relat_1 @ A @ B ) = ( A ) ) ) =>
% 17.28/17.47             ( ( B ) = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 17.28/17.47  thf('171', plain,
% 17.28/17.47      (![X14 : $i, X15 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X14)
% 17.28/17.47          | ~ (v1_funct_1 @ X14)
% 17.28/17.47          | ((X14) = (k6_relat_1 @ (k1_relat_1 @ X14)))
% 17.28/17.47          | ((k5_relat_1 @ X15 @ X14) != (X15))
% 17.28/17.47          | ((k2_relat_1 @ X15) != (k1_relat_1 @ X14))
% 17.28/17.47          | ~ (v1_funct_1 @ X15)
% 17.28/17.47          | ~ (v1_relat_1 @ X15))),
% 17.28/17.47      inference('cnf', [status(esa)], [t44_funct_1])).
% 17.28/17.47  thf('172', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (((k2_relat_1 @ X0) != (k2_relat_1 @ sk_B))
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | ((k5_relat_1 @ X0 @ (k5_relat_1 @ sk_A @ sk_B)) != (X0))
% 17.28/17.47          | ((k5_relat_1 @ sk_A @ sk_B)
% 17.28/17.47              = (k6_relat_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 17.28/17.47          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 17.28/17.47          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 17.28/17.47      inference('sup-', [status(thm)], ['170', '171'])).
% 17.28/17.47  thf('173', plain,
% 17.28/17.47      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) = (k2_relat_1 @ sk_B))),
% 17.28/17.47      inference('demod', [status(thm)], ['133', '139', '140', '141'])).
% 17.28/17.47  thf('174', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (((k2_relat_1 @ X0) != (k2_relat_1 @ sk_B))
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | ((k5_relat_1 @ X0 @ (k5_relat_1 @ sk_A @ sk_B)) != (X0))
% 17.28/17.47          | ((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 17.28/17.47          | ~ (v1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 17.28/17.47          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 17.28/17.47      inference('demod', [status(thm)], ['172', '173'])).
% 17.28/17.47  thf('175', plain,
% 17.28/17.47      (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 17.28/17.47         (k5_relat_1 @ sk_A @ sk_B)) = (k5_relat_1 @ sk_A @ sk_B))),
% 17.28/17.47      inference('demod', [status(thm)], ['145', '146', '147'])).
% 17.28/17.47  thf(fc2_funct_1, axiom,
% 17.28/17.47    (![A:$i,B:$i]:
% 17.28/17.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 17.28/17.47         ( v1_funct_1 @ B ) ) =>
% 17.28/17.47       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 17.28/17.47         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 17.28/17.47  thf('176', plain,
% 17.28/17.47      (![X12 : $i, X13 : $i]:
% 17.28/17.47         (~ (v1_funct_1 @ X12)
% 17.28/17.47          | ~ (v1_relat_1 @ X12)
% 17.28/17.47          | ~ (v1_relat_1 @ X13)
% 17.28/17.47          | ~ (v1_funct_1 @ X13)
% 17.28/17.47          | (v1_funct_1 @ (k5_relat_1 @ X12 @ X13)))),
% 17.28/17.47      inference('cnf', [status(esa)], [fc2_funct_1])).
% 17.28/17.47  thf('177', plain,
% 17.28/17.47      (![X0 : $i, X1 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 17.28/17.47      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 17.28/17.47  thf('178', plain,
% 17.28/17.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X5)
% 17.28/17.47          | ((k5_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 17.28/17.47              = (k5_relat_1 @ X6 @ (k5_relat_1 @ X5 @ X7)))
% 17.28/17.47          | ~ (v1_relat_1 @ X7)
% 17.28/17.47          | ~ (v1_relat_1 @ X6))),
% 17.28/17.47      inference('cnf', [status(esa)], [t55_relat_1])).
% 17.28/17.47  thf('179', plain,
% 17.28/17.47      (![X12 : $i, X13 : $i]:
% 17.28/17.47         (~ (v1_funct_1 @ X12)
% 17.28/17.47          | ~ (v1_relat_1 @ X12)
% 17.28/17.47          | ~ (v1_relat_1 @ X13)
% 17.28/17.47          | ~ (v1_funct_1 @ X13)
% 17.28/17.47          | (v1_funct_1 @ (k5_relat_1 @ X12 @ X13)))),
% 17.28/17.47      inference('cnf', [status(esa)], [fc2_funct_1])).
% 17.28/17.47  thf('180', plain,
% 17.28/17.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.28/17.47         ((v1_funct_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ X2)
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 17.28/17.47          | ~ (v1_funct_1 @ (k5_relat_1 @ X2 @ X1)))),
% 17.28/17.47      inference('sup+', [status(thm)], ['178', '179'])).
% 17.28/17.47  thf('181', plain,
% 17.28/17.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.28/17.47         (~ (v1_funct_1 @ (k5_relat_1 @ X2 @ X1))
% 17.28/17.47          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X2)
% 17.28/17.47          | (v1_funct_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 17.28/17.47      inference('simplify', [status(thm)], ['180'])).
% 17.28/17.47  thf('182', plain,
% 17.28/17.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | (v1_funct_1 @ (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | ~ (v1_relat_1 @ X2)
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ X2)
% 17.28/17.47          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 17.28/17.47      inference('sup-', [status(thm)], ['177', '181'])).
% 17.28/17.47  thf('183', plain,
% 17.28/17.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.28/17.47         (~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 17.28/17.47          | ~ (v1_funct_1 @ X2)
% 17.28/17.47          | ~ (v1_relat_1 @ X2)
% 17.28/17.47          | (v1_funct_1 @ (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | ~ (v1_relat_1 @ X0))),
% 17.28/17.47      inference('simplify', [status(thm)], ['182'])).
% 17.28/17.47  thf('184', plain,
% 17.28/17.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.28/17.47         (~ (v1_funct_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | ~ (v1_funct_1 @ X1)
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | (v1_funct_1 @ (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 17.28/17.47          | ~ (v1_relat_1 @ X2)
% 17.28/17.47          | ~ (v1_funct_1 @ X2))),
% 17.28/17.47      inference('sup-', [status(thm)], ['176', '183'])).
% 17.28/17.47  thf('185', plain,
% 17.28/17.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.28/17.47         (~ (v1_funct_1 @ X2)
% 17.28/17.47          | ~ (v1_relat_1 @ X2)
% 17.28/17.47          | (v1_funct_1 @ (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 17.28/17.47          | ~ (v1_funct_1 @ X1)
% 17.28/17.47          | ~ (v1_relat_1 @ X1)
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ X0))),
% 17.28/17.47      inference('simplify', [status(thm)], ['184'])).
% 17.28/17.47  thf('186', plain,
% 17.28/17.47      (((v1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 17.28/17.47        | ~ (v1_funct_1 @ sk_A)
% 17.28/17.47        | ~ (v1_relat_1 @ sk_A)
% 17.28/17.47        | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 17.28/17.47        | ~ (v1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 17.28/17.47        | ~ (v1_relat_1 @ sk_B)
% 17.28/17.47        | ~ (v1_funct_1 @ sk_B))),
% 17.28/17.47      inference('sup+', [status(thm)], ['175', '185'])).
% 17.28/17.47  thf('187', plain, ((v1_funct_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('188', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('189', plain, ((v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 17.28/17.47      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 17.28/17.47  thf('190', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('191', plain,
% 17.28/17.47      (![X11 : $i]:
% 17.28/17.47         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 17.28/17.47          | ~ (v1_funct_1 @ X11)
% 17.28/17.47          | ~ (v1_relat_1 @ X11))),
% 17.28/17.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 17.28/17.47  thf('192', plain,
% 17.28/17.47      (![X11 : $i]:
% 17.28/17.47         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 17.28/17.47          | ~ (v1_funct_1 @ X11)
% 17.28/17.47          | ~ (v1_relat_1 @ X11))),
% 17.28/17.47      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 17.28/17.47  thf('193', plain,
% 17.28/17.47      (![X17 : $i]:
% 17.28/17.47         (~ (v2_funct_1 @ X17)
% 17.28/17.47          | ((k5_relat_1 @ X17 @ (k2_funct_1 @ X17))
% 17.28/17.47              = (k6_relat_1 @ (k1_relat_1 @ X17)))
% 17.28/17.47          | ~ (v1_funct_1 @ X17)
% 17.28/17.47          | ~ (v1_relat_1 @ X17))),
% 17.28/17.47      inference('cnf', [status(esa)], [t61_funct_1])).
% 17.28/17.47  thf('194', plain,
% 17.28/17.47      (![X12 : $i, X13 : $i]:
% 17.28/17.47         (~ (v1_funct_1 @ X12)
% 17.28/17.47          | ~ (v1_relat_1 @ X12)
% 17.28/17.47          | ~ (v1_relat_1 @ X13)
% 17.28/17.47          | ~ (v1_funct_1 @ X13)
% 17.28/17.47          | (v1_funct_1 @ (k5_relat_1 @ X12 @ X13)))),
% 17.28/17.47      inference('cnf', [status(esa)], [fc2_funct_1])).
% 17.28/17.47  thf('195', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         ((v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | ~ (v2_funct_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 17.28/17.47          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ X0))),
% 17.28/17.47      inference('sup+', [status(thm)], ['193', '194'])).
% 17.28/17.47  thf('196', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 17.28/17.47          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 17.28/17.47          | ~ (v2_funct_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | (v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 17.28/17.47      inference('simplify', [status(thm)], ['195'])).
% 17.28/17.47  thf('197', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | (v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | ~ (v2_funct_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 17.28/17.47      inference('sup-', [status(thm)], ['192', '196'])).
% 17.28/17.47  thf('198', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 17.28/17.47          | ~ (v2_funct_1 @ X0)
% 17.28/17.47          | (v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X0))),
% 17.28/17.47      inference('simplify', [status(thm)], ['197'])).
% 17.28/17.47  thf('199', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | (v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 17.28/17.47          | ~ (v2_funct_1 @ X0))),
% 17.28/17.47      inference('sup-', [status(thm)], ['191', '198'])).
% 17.28/17.47  thf('200', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (~ (v2_funct_1 @ X0)
% 17.28/17.47          | (v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | ~ (v1_relat_1 @ X0))),
% 17.28/17.47      inference('simplify', [status(thm)], ['199'])).
% 17.28/17.47  thf('201', plain,
% 17.28/17.47      (((v1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 17.28/17.47        | ~ (v1_relat_1 @ sk_A)
% 17.28/17.47        | ~ (v1_funct_1 @ sk_A)
% 17.28/17.47        | ~ (v2_funct_1 @ sk_A))),
% 17.28/17.47      inference('sup+', [status(thm)], ['190', '200'])).
% 17.28/17.47  thf('202', plain, ((v1_relat_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('203', plain, ((v1_funct_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('204', plain, ((v2_funct_1 @ sk_A)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('205', plain, ((v1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 17.28/17.47      inference('demod', [status(thm)], ['201', '202', '203', '204'])).
% 17.28/17.47  thf('206', plain, ((v1_relat_1 @ sk_B)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('207', plain, ((v1_funct_1 @ sk_B)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('208', plain, ((v1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B))),
% 17.28/17.47      inference('demod', [status(thm)],
% 17.28/17.47                ['186', '187', '188', '189', '205', '206', '207'])).
% 17.28/17.47  thf('209', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))),
% 17.28/17.47      inference('demod', [status(thm)], ['159', '160', '161', '162'])).
% 17.28/17.47  thf('210', plain,
% 17.28/17.47      (![X0 : $i]:
% 17.28/17.47         (((k2_relat_1 @ X0) != (k2_relat_1 @ sk_B))
% 17.28/17.47          | ~ (v1_relat_1 @ X0)
% 17.28/17.47          | ~ (v1_funct_1 @ X0)
% 17.28/17.47          | ((k5_relat_1 @ X0 @ (k5_relat_1 @ sk_A @ sk_B)) != (X0))
% 17.28/17.47          | ((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 17.28/17.47      inference('demod', [status(thm)], ['174', '208', '209'])).
% 17.28/17.47  thf('211', plain,
% 17.28/17.47      ((((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B) != (sk_B))
% 17.28/17.47        | ~ (v1_relat_1 @ sk_B)
% 17.28/17.47        | ((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 17.28/17.47        | ~ (v1_funct_1 @ sk_B)
% 17.28/17.47        | ~ (v1_relat_1 @ sk_B)
% 17.28/17.47        | ((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B)))),
% 17.28/17.47      inference('sup-', [status(thm)], ['169', '210'])).
% 17.28/17.47  thf('212', plain, ((v1_relat_1 @ sk_B)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('213', plain, ((v1_funct_1 @ sk_B)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('214', plain, ((v1_relat_1 @ sk_B)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('215', plain,
% 17.28/17.47      ((((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B) != (sk_B))
% 17.28/17.47        | ((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 17.28/17.47        | ((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B)))),
% 17.28/17.47      inference('demod', [status(thm)], ['211', '212', '213', '214'])).
% 17.28/17.47  thf('216', plain,
% 17.28/17.47      ((((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 17.28/17.47        | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B) != (sk_B)))),
% 17.28/17.47      inference('simplify', [status(thm)], ['215'])).
% 17.28/17.47  thf('217', plain,
% 17.28/17.47      ((((sk_B) != (sk_B))
% 17.28/17.47        | ~ (v1_relat_1 @ sk_B)
% 17.28/17.47        | ((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 17.28/17.47      inference('sup-', [status(thm)], ['168', '216'])).
% 17.28/17.47  thf('218', plain, ((v1_relat_1 @ sk_B)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('219', plain,
% 17.28/17.47      ((((sk_B) != (sk_B))
% 17.28/17.47        | ((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 17.28/17.47      inference('demod', [status(thm)], ['217', '218'])).
% 17.28/17.47  thf('220', plain,
% 17.28/17.47      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 17.28/17.47      inference('simplify', [status(thm)], ['219'])).
% 17.28/17.47  thf('221', plain,
% 17.28/17.47      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B)
% 17.28/17.47         = (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 17.28/17.47      inference('demod', [status(thm)], ['167', '220'])).
% 17.28/17.47  thf('222', plain,
% 17.28/17.47      (((k2_funct_1 @ sk_A)
% 17.28/17.47         = (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 17.28/17.47      inference('demod', [status(thm)], ['45', '46', '47'])).
% 17.28/17.47  thf('223', plain,
% 17.28/17.47      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B)
% 17.28/17.47         = (k2_funct_1 @ sk_A))),
% 17.28/17.47      inference('demod', [status(thm)], ['221', '222'])).
% 17.28/17.47  thf('224', plain, ((((sk_B) = (k2_funct_1 @ sk_A)) | ~ (v1_relat_1 @ sk_B))),
% 17.28/17.47      inference('sup+', [status(thm)], ['0', '223'])).
% 17.28/17.47  thf('225', plain, ((v1_relat_1 @ sk_B)),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('226', plain, (((sk_B) = (k2_funct_1 @ sk_A))),
% 17.28/17.47      inference('demod', [status(thm)], ['224', '225'])).
% 17.28/17.47  thf('227', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 17.28/17.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.28/17.47  thf('228', plain, ($false),
% 17.28/17.47      inference('simplify_reflect-', [status(thm)], ['226', '227'])).
% 17.28/17.47  
% 17.28/17.47  % SZS output end Refutation
% 17.28/17.47  
% 17.28/17.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

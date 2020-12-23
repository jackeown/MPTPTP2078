%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VAw3PH2xPW

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:42 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 478 expanded)
%              Number of leaves         :   22 ( 153 expanded)
%              Depth                    :   16
%              Number of atoms          : 1067 (7045 expanded)
%              Number of equality atoms :   86 ( 727 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf('0',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X7 ) )
      = ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('2',plain,
    ( ( k4_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k4_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
    = ( k5_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X2 ) @ ( k4_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ sk_B @ sk_A ) ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('9',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ sk_B @ sk_A ) ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k5_relat_1 @ X16 @ ( k2_funct_1 @ X16 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k5_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('13',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k7_relat_1 @ X10 @ X9 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X9 ) @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k2_relat_1 @ sk_A ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k2_relat_1 @ sk_A ) )
        = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k2_relat_1 @ sk_A ) )
        = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k2_relat_1 @ sk_A ) )
        = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( k7_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
      = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('23',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('24',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_funct_1 @ sk_A )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('29',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('30',plain,
    ( ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
      = sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('37',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('38',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('39',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,
    ( ( k7_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['21','27','32','33','34','35','36','43'])).

thf('45',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('46',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k7_relat_1 @ X10 @ X9 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X9 ) @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('47',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k5_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['45','51'])).

thf('53',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ ( k4_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['44','55'])).

thf('57',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X2 ) @ ( k4_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('58',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('59',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('60',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_A ) )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) )
      = ( k4_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('64',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('65',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('71',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('72',plain,(
    ! [X15: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('73',plain,
    ( ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('78',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('79',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('80',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_A ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','69','70','77','78','79','80','81','82'])).

thf('84',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X16 ) @ X16 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('85',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) @ ( k4_relat_1 @ sk_A ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('87',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('88',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('89',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) @ ( k4_relat_1 @ sk_A ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,
    ( ( ( k4_relat_1 @ ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['57','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('93',plain,
    ( ( k4_relat_1 @ ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('95',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k5_relat_1 @ X16 @ ( k2_funct_1 @ X16 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('96',plain,
    ( ( ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97','98','99'])).

thf('101',plain,(
    ! [X7: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X7 ) )
      = ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('102',plain,
    ( ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['93','100','101'])).

thf('103',plain,
    ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['30','31'])).

thf('104',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('106',plain,
    ( sk_B
    = ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','102','103','104','105'])).

thf('107',plain,
    ( ( sk_B
      = ( k4_relat_1 @ ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['10','106'])).

thf('108',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('110',plain,
    ( ( ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( sk_B
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['107','112','113'])).

thf('115',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('117',plain,(
    sk_B
 != ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['114','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VAw3PH2xPW
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.86  % Solved by: fo/fo7.sh
% 0.68/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.86  % done 518 iterations in 0.408s
% 0.68/0.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.86  % SZS output start Refutation
% 0.68/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.86  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.68/0.86  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.68/0.86  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.68/0.86  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.68/0.86  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.68/0.86  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.68/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.86  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.68/0.86  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.68/0.86  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.68/0.86  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.68/0.86  thf(t64_funct_1, conjecture,
% 0.68/0.86    (![A:$i]:
% 0.68/0.86     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.68/0.86       ( ![B:$i]:
% 0.68/0.86         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.68/0.86           ( ( ( v2_funct_1 @ A ) & 
% 0.68/0.86               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.68/0.86               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.68/0.86             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.68/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.86    (~( ![A:$i]:
% 0.68/0.86        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.68/0.86          ( ![B:$i]:
% 0.68/0.86            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.68/0.86              ( ( ( v2_funct_1 @ A ) & 
% 0.68/0.86                  ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.68/0.86                  ( ( k5_relat_1 @ B @ A ) =
% 0.68/0.86                    ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.68/0.86                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.68/0.86    inference('cnf.neg', [status(esa)], [t64_funct_1])).
% 0.68/0.86  thf('0', plain,
% 0.68/0.86      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(t72_relat_1, axiom,
% 0.68/0.86    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.68/0.86  thf('1', plain,
% 0.68/0.86      (![X7 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X7)) = (k6_relat_1 @ X7))),
% 0.68/0.86      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.68/0.86  thf('2', plain,
% 0.68/0.86      (((k4_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))
% 0.68/0.86         = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.68/0.86      inference('sup+', [status(thm)], ['0', '1'])).
% 0.68/0.86  thf('3', plain,
% 0.68/0.86      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('4', plain,
% 0.68/0.86      (((k4_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)) = (k5_relat_1 @ sk_B @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['2', '3'])).
% 0.68/0.86  thf(t54_relat_1, axiom,
% 0.68/0.86    (![A:$i]:
% 0.68/0.86     ( ( v1_relat_1 @ A ) =>
% 0.68/0.86       ( ![B:$i]:
% 0.68/0.86         ( ( v1_relat_1 @ B ) =>
% 0.68/0.86           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.68/0.86             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.68/0.86  thf('5', plain,
% 0.68/0.86      (![X2 : $i, X3 : $i]:
% 0.68/0.86         (~ (v1_relat_1 @ X2)
% 0.68/0.86          | ((k4_relat_1 @ (k5_relat_1 @ X3 @ X2))
% 0.68/0.86              = (k5_relat_1 @ (k4_relat_1 @ X2) @ (k4_relat_1 @ X3)))
% 0.68/0.86          | ~ (v1_relat_1 @ X3))),
% 0.68/0.86      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.68/0.86  thf('6', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         (((k4_relat_1 @ (k5_relat_1 @ X0 @ (k5_relat_1 @ sk_B @ sk_A)))
% 0.68/0.86            = (k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ (k4_relat_1 @ X0)))
% 0.68/0.86          | ~ (v1_relat_1 @ X0)
% 0.68/0.86          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)))),
% 0.68/0.86      inference('sup+', [status(thm)], ['4', '5'])).
% 0.68/0.86  thf('7', plain,
% 0.68/0.86      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(fc3_funct_1, axiom,
% 0.68/0.86    (![A:$i]:
% 0.68/0.86     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.68/0.86       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.68/0.86  thf('8', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.68/0.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.68/0.86  thf('9', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))),
% 0.68/0.86      inference('sup+', [status(thm)], ['7', '8'])).
% 0.68/0.86  thf('10', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         (((k4_relat_1 @ (k5_relat_1 @ X0 @ (k5_relat_1 @ sk_B @ sk_A)))
% 0.68/0.86            = (k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ (k4_relat_1 @ X0)))
% 0.68/0.86          | ~ (v1_relat_1 @ X0))),
% 0.68/0.86      inference('demod', [status(thm)], ['6', '9'])).
% 0.68/0.86  thf(t61_funct_1, axiom,
% 0.68/0.86    (![A:$i]:
% 0.68/0.86     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.68/0.86       ( ( v2_funct_1 @ A ) =>
% 0.68/0.86         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.68/0.86             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.68/0.86           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.68/0.86             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.68/0.86  thf('11', plain,
% 0.68/0.86      (![X16 : $i]:
% 0.68/0.86         (~ (v2_funct_1 @ X16)
% 0.68/0.86          | ((k5_relat_1 @ X16 @ (k2_funct_1 @ X16))
% 0.68/0.86              = (k6_relat_1 @ (k1_relat_1 @ X16)))
% 0.68/0.86          | ~ (v1_funct_1 @ X16)
% 0.68/0.86          | ~ (v1_relat_1 @ X16))),
% 0.68/0.86      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.68/0.86  thf(t55_relat_1, axiom,
% 0.68/0.86    (![A:$i]:
% 0.68/0.86     ( ( v1_relat_1 @ A ) =>
% 0.68/0.86       ( ![B:$i]:
% 0.68/0.86         ( ( v1_relat_1 @ B ) =>
% 0.68/0.86           ( ![C:$i]:
% 0.68/0.86             ( ( v1_relat_1 @ C ) =>
% 0.68/0.86               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.68/0.86                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.68/0.86  thf('12', plain,
% 0.68/0.86      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.68/0.86         (~ (v1_relat_1 @ X4)
% 0.68/0.86          | ((k5_relat_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 0.68/0.86              = (k5_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X6)))
% 0.68/0.86          | ~ (v1_relat_1 @ X6)
% 0.68/0.86          | ~ (v1_relat_1 @ X5))),
% 0.68/0.86      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.68/0.86  thf('13', plain,
% 0.68/0.86      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(t94_relat_1, axiom,
% 0.68/0.86    (![A:$i,B:$i]:
% 0.68/0.86     ( ( v1_relat_1 @ B ) =>
% 0.68/0.86       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.68/0.86  thf('14', plain,
% 0.68/0.86      (![X9 : $i, X10 : $i]:
% 0.68/0.86         (((k7_relat_1 @ X10 @ X9) = (k5_relat_1 @ (k6_relat_1 @ X9) @ X10))
% 0.68/0.86          | ~ (v1_relat_1 @ X10))),
% 0.68/0.86      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.68/0.86  thf('15', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         (((k7_relat_1 @ X0 @ (k2_relat_1 @ sk_A))
% 0.68/0.86            = (k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ X0))
% 0.68/0.86          | ~ (v1_relat_1 @ X0))),
% 0.68/0.86      inference('sup+', [status(thm)], ['13', '14'])).
% 0.68/0.86  thf('16', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         (((k7_relat_1 @ X0 @ (k2_relat_1 @ sk_A))
% 0.68/0.86            = (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ X0)))
% 0.68/0.86          | ~ (v1_relat_1 @ sk_B)
% 0.68/0.86          | ~ (v1_relat_1 @ X0)
% 0.68/0.86          | ~ (v1_relat_1 @ sk_A)
% 0.68/0.86          | ~ (v1_relat_1 @ X0))),
% 0.68/0.86      inference('sup+', [status(thm)], ['12', '15'])).
% 0.68/0.86  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('19', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         (((k7_relat_1 @ X0 @ (k2_relat_1 @ sk_A))
% 0.68/0.86            = (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ X0)))
% 0.68/0.86          | ~ (v1_relat_1 @ X0)
% 0.68/0.86          | ~ (v1_relat_1 @ X0))),
% 0.68/0.86      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.68/0.86  thf('20', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         (~ (v1_relat_1 @ X0)
% 0.68/0.86          | ((k7_relat_1 @ X0 @ (k2_relat_1 @ sk_A))
% 0.68/0.86              = (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ X0))))),
% 0.68/0.86      inference('simplify', [status(thm)], ['19'])).
% 0.68/0.86  thf('21', plain,
% 0.68/0.86      ((((k7_relat_1 @ (k2_funct_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.68/0.86          = (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.68/0.86        | ~ (v1_relat_1 @ sk_A)
% 0.68/0.86        | ~ (v1_funct_1 @ sk_A)
% 0.68/0.86        | ~ (v2_funct_1 @ sk_A)
% 0.68/0.86        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.68/0.86      inference('sup+', [status(thm)], ['11', '20'])).
% 0.68/0.86  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(d9_funct_1, axiom,
% 0.68/0.86    (![A:$i]:
% 0.68/0.86     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.68/0.86       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.68/0.86  thf('23', plain,
% 0.68/0.86      (![X12 : $i]:
% 0.68/0.86         (~ (v2_funct_1 @ X12)
% 0.68/0.86          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 0.68/0.86          | ~ (v1_funct_1 @ X12)
% 0.68/0.86          | ~ (v1_relat_1 @ X12))),
% 0.68/0.86      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.68/0.86  thf('24', plain,
% 0.68/0.86      ((~ (v1_funct_1 @ sk_A)
% 0.68/0.86        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))
% 0.68/0.86        | ~ (v2_funct_1 @ sk_A))),
% 0.68/0.86      inference('sup-', [status(thm)], ['22', '23'])).
% 0.68/0.86  thf('25', plain, ((v1_funct_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('26', plain, ((v2_funct_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('27', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.68/0.86  thf('28', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(t80_relat_1, axiom,
% 0.68/0.86    (![A:$i]:
% 0.68/0.86     ( ( v1_relat_1 @ A ) =>
% 0.68/0.86       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.68/0.86  thf('29', plain,
% 0.68/0.86      (![X8 : $i]:
% 0.68/0.86         (((k5_relat_1 @ X8 @ (k6_relat_1 @ (k2_relat_1 @ X8))) = (X8))
% 0.68/0.86          | ~ (v1_relat_1 @ X8))),
% 0.68/0.86      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.68/0.86  thf('30', plain,
% 0.68/0.86      ((((k5_relat_1 @ sk_B @ (k6_relat_1 @ (k1_relat_1 @ sk_A))) = (sk_B))
% 0.68/0.86        | ~ (v1_relat_1 @ sk_B))),
% 0.68/0.86      inference('sup+', [status(thm)], ['28', '29'])).
% 0.68/0.86  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('32', plain,
% 0.68/0.86      (((k5_relat_1 @ sk_B @ (k6_relat_1 @ (k1_relat_1 @ sk_A))) = (sk_B))),
% 0.68/0.86      inference('demod', [status(thm)], ['30', '31'])).
% 0.68/0.86  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('34', plain, ((v1_funct_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('35', plain, ((v2_funct_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('36', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.68/0.86  thf('37', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.68/0.86  thf(fc6_funct_1, axiom,
% 0.68/0.86    (![A:$i]:
% 0.68/0.86     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.68/0.86       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.68/0.86         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.68/0.86         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.68/0.86  thf('38', plain,
% 0.68/0.86      (![X15 : $i]:
% 0.68/0.86         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.68/0.86          | ~ (v2_funct_1 @ X15)
% 0.68/0.86          | ~ (v1_funct_1 @ X15)
% 0.68/0.86          | ~ (v1_relat_1 @ X15))),
% 0.68/0.86      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.68/0.86  thf('39', plain,
% 0.68/0.86      (((v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.68/0.86        | ~ (v1_relat_1 @ sk_A)
% 0.68/0.86        | ~ (v1_funct_1 @ sk_A)
% 0.68/0.86        | ~ (v2_funct_1 @ sk_A))),
% 0.68/0.86      inference('sup+', [status(thm)], ['37', '38'])).
% 0.68/0.86  thf('40', plain, ((v1_relat_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('41', plain, ((v1_funct_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('42', plain, ((v2_funct_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('43', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.68/0.86  thf('44', plain,
% 0.68/0.86      (((k7_relat_1 @ (k4_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) = (sk_B))),
% 0.68/0.86      inference('demod', [status(thm)],
% 0.68/0.86                ['21', '27', '32', '33', '34', '35', '36', '43'])).
% 0.68/0.86  thf('45', plain,
% 0.68/0.86      (![X8 : $i]:
% 0.68/0.86         (((k5_relat_1 @ X8 @ (k6_relat_1 @ (k2_relat_1 @ X8))) = (X8))
% 0.68/0.86          | ~ (v1_relat_1 @ X8))),
% 0.68/0.86      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.68/0.86  thf('46', plain,
% 0.68/0.86      (![X9 : $i, X10 : $i]:
% 0.68/0.86         (((k7_relat_1 @ X10 @ X9) = (k5_relat_1 @ (k6_relat_1 @ X9) @ X10))
% 0.68/0.86          | ~ (v1_relat_1 @ X10))),
% 0.68/0.86      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.68/0.86  thf('47', plain,
% 0.68/0.86      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.68/0.86         (~ (v1_relat_1 @ X4)
% 0.68/0.86          | ((k5_relat_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 0.68/0.86              = (k5_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X6)))
% 0.68/0.86          | ~ (v1_relat_1 @ X6)
% 0.68/0.86          | ~ (v1_relat_1 @ X5))),
% 0.68/0.86      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.68/0.86  thf('48', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.68/0.86            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 0.68/0.86          | ~ (v1_relat_1 @ X1)
% 0.68/0.86          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.68/0.86          | ~ (v1_relat_1 @ X2)
% 0.68/0.86          | ~ (v1_relat_1 @ X1))),
% 0.68/0.86      inference('sup+', [status(thm)], ['46', '47'])).
% 0.68/0.86  thf('49', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.68/0.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.68/0.86  thf('50', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.68/0.86            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 0.68/0.86          | ~ (v1_relat_1 @ X1)
% 0.68/0.86          | ~ (v1_relat_1 @ X2)
% 0.68/0.86          | ~ (v1_relat_1 @ X1))),
% 0.68/0.86      inference('demod', [status(thm)], ['48', '49'])).
% 0.68/0.86  thf('51', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         (~ (v1_relat_1 @ X2)
% 0.68/0.86          | ~ (v1_relat_1 @ X1)
% 0.68/0.86          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.68/0.86              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 0.68/0.86      inference('simplify', [status(thm)], ['50'])).
% 0.68/0.86  thf('52', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         (((k5_relat_1 @ (k7_relat_1 @ X0 @ X1) @ 
% 0.68/0.86            (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.68/0.86            = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.68/0.86          | ~ (v1_relat_1 @ X0)
% 0.68/0.86          | ~ (v1_relat_1 @ X0)
% 0.68/0.86          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 0.68/0.86      inference('sup+', [status(thm)], ['45', '51'])).
% 0.68/0.86  thf('53', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.68/0.86      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.68/0.86  thf('54', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         (((k5_relat_1 @ (k7_relat_1 @ X0 @ X1) @ 
% 0.68/0.86            (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.68/0.86            = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.68/0.86          | ~ (v1_relat_1 @ X0)
% 0.68/0.86          | ~ (v1_relat_1 @ X0))),
% 0.68/0.86      inference('demod', [status(thm)], ['52', '53'])).
% 0.68/0.86  thf('55', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         (~ (v1_relat_1 @ X0)
% 0.68/0.86          | ((k5_relat_1 @ (k7_relat_1 @ X0 @ X1) @ 
% 0.68/0.86              (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.68/0.86              = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.68/0.86      inference('simplify', [status(thm)], ['54'])).
% 0.68/0.86  thf('56', plain,
% 0.68/0.86      ((((k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A))))
% 0.68/0.86          = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ 
% 0.68/0.86             (k4_relat_1 @ sk_A)))
% 0.68/0.86        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.68/0.86      inference('sup+', [status(thm)], ['44', '55'])).
% 0.68/0.86  thf('57', plain,
% 0.68/0.86      (![X2 : $i, X3 : $i]:
% 0.68/0.86         (~ (v1_relat_1 @ X2)
% 0.68/0.86          | ((k4_relat_1 @ (k5_relat_1 @ X3 @ X2))
% 0.68/0.86              = (k5_relat_1 @ (k4_relat_1 @ X2) @ (k4_relat_1 @ X3)))
% 0.68/0.86          | ~ (v1_relat_1 @ X3))),
% 0.68/0.86      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.68/0.86  thf('58', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.68/0.86  thf('59', plain,
% 0.68/0.86      (![X15 : $i]:
% 0.68/0.86         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.68/0.86          | ~ (v2_funct_1 @ X15)
% 0.68/0.86          | ~ (v1_funct_1 @ X15)
% 0.68/0.86          | ~ (v1_relat_1 @ X15))),
% 0.68/0.86      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.68/0.86  thf('60', plain,
% 0.68/0.86      (![X12 : $i]:
% 0.68/0.86         (~ (v2_funct_1 @ X12)
% 0.68/0.86          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 0.68/0.86          | ~ (v1_funct_1 @ X12)
% 0.68/0.86          | ~ (v1_relat_1 @ X12))),
% 0.68/0.86      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.68/0.86  thf('61', plain,
% 0.68/0.86      (![X0 : $i]:
% 0.68/0.86         (~ (v1_relat_1 @ X0)
% 0.68/0.86          | ~ (v1_funct_1 @ X0)
% 0.68/0.86          | ~ (v2_funct_1 @ X0)
% 0.68/0.86          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.68/0.86          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 0.68/0.86              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 0.68/0.86          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.68/0.86      inference('sup-', [status(thm)], ['59', '60'])).
% 0.68/0.86  thf('62', plain,
% 0.68/0.86      ((~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.68/0.86        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_A))
% 0.68/0.86        | ((k2_funct_1 @ (k2_funct_1 @ sk_A))
% 0.68/0.86            = (k4_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.68/0.86        | ~ (v2_funct_1 @ sk_A)
% 0.68/0.86        | ~ (v1_funct_1 @ sk_A)
% 0.68/0.86        | ~ (v1_relat_1 @ sk_A))),
% 0.68/0.86      inference('sup-', [status(thm)], ['58', '61'])).
% 0.68/0.86  thf('63', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.68/0.86  thf('64', plain,
% 0.68/0.86      (![X15 : $i]:
% 0.68/0.86         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 0.68/0.86          | ~ (v2_funct_1 @ X15)
% 0.68/0.86          | ~ (v1_funct_1 @ X15)
% 0.68/0.86          | ~ (v1_relat_1 @ X15))),
% 0.68/0.86      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.68/0.86  thf('65', plain,
% 0.68/0.86      (((v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.68/0.86        | ~ (v1_relat_1 @ sk_A)
% 0.68/0.86        | ~ (v1_funct_1 @ sk_A)
% 0.68/0.86        | ~ (v2_funct_1 @ sk_A))),
% 0.68/0.86      inference('sup+', [status(thm)], ['63', '64'])).
% 0.68/0.86  thf('66', plain, ((v1_relat_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('67', plain, ((v1_funct_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('68', plain, ((v2_funct_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('69', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.68/0.86  thf('70', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.68/0.86  thf('71', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.68/0.86  thf('72', plain,
% 0.68/0.86      (![X15 : $i]:
% 0.68/0.86         ((v2_funct_1 @ (k2_funct_1 @ X15))
% 0.68/0.86          | ~ (v2_funct_1 @ X15)
% 0.68/0.86          | ~ (v1_funct_1 @ X15)
% 0.68/0.86          | ~ (v1_relat_1 @ X15))),
% 0.68/0.86      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.68/0.86  thf('73', plain,
% 0.68/0.86      (((v2_funct_1 @ (k4_relat_1 @ sk_A))
% 0.68/0.86        | ~ (v1_relat_1 @ sk_A)
% 0.68/0.86        | ~ (v1_funct_1 @ sk_A)
% 0.68/0.86        | ~ (v2_funct_1 @ sk_A))),
% 0.68/0.86      inference('sup+', [status(thm)], ['71', '72'])).
% 0.68/0.86  thf('74', plain, ((v1_relat_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('75', plain, ((v1_funct_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('76', plain, ((v2_funct_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('77', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 0.68/0.86  thf('78', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.68/0.86  thf('79', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.68/0.86  thf('80', plain, ((v2_funct_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('81', plain, ((v1_funct_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('82', plain, ((v1_relat_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('83', plain,
% 0.68/0.86      (((k2_funct_1 @ (k4_relat_1 @ sk_A)) = (k4_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.68/0.86      inference('demod', [status(thm)],
% 0.68/0.86                ['62', '69', '70', '77', '78', '79', '80', '81', '82'])).
% 0.68/0.86  thf('84', plain,
% 0.68/0.86      (![X16 : $i]:
% 0.68/0.86         (~ (v2_funct_1 @ X16)
% 0.68/0.86          | ((k5_relat_1 @ (k2_funct_1 @ X16) @ X16)
% 0.68/0.86              = (k6_relat_1 @ (k2_relat_1 @ X16)))
% 0.68/0.86          | ~ (v1_funct_1 @ X16)
% 0.68/0.86          | ~ (v1_relat_1 @ X16))),
% 0.68/0.86      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.68/0.86  thf('85', plain,
% 0.68/0.86      ((((k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_A)) @ (k4_relat_1 @ sk_A))
% 0.68/0.86          = (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A))))
% 0.68/0.86        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.68/0.86        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 0.68/0.86        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_A)))),
% 0.68/0.86      inference('sup+', [status(thm)], ['83', '84'])).
% 0.68/0.86  thf('86', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.68/0.86  thf('87', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.68/0.86  thf('88', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 0.68/0.86  thf('89', plain,
% 0.68/0.86      (((k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_A)) @ (k4_relat_1 @ sk_A))
% 0.68/0.86         = (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A))))),
% 0.68/0.86      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 0.68/0.86  thf('90', plain,
% 0.68/0.86      ((((k4_relat_1 @ (k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A)))
% 0.68/0.86          = (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A))))
% 0.68/0.86        | ~ (v1_relat_1 @ sk_A)
% 0.68/0.86        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 0.68/0.86      inference('sup+', [status(thm)], ['57', '89'])).
% 0.68/0.86  thf('91', plain, ((v1_relat_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('92', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.68/0.86  thf('93', plain,
% 0.68/0.86      (((k4_relat_1 @ (k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A)))
% 0.68/0.86         = (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A))))),
% 0.68/0.86      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.68/0.86  thf('94', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.68/0.86  thf('95', plain,
% 0.68/0.86      (![X16 : $i]:
% 0.68/0.86         (~ (v2_funct_1 @ X16)
% 0.68/0.86          | ((k5_relat_1 @ X16 @ (k2_funct_1 @ X16))
% 0.68/0.86              = (k6_relat_1 @ (k1_relat_1 @ X16)))
% 0.68/0.86          | ~ (v1_funct_1 @ X16)
% 0.68/0.86          | ~ (v1_relat_1 @ X16))),
% 0.68/0.86      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.68/0.86  thf('96', plain,
% 0.68/0.86      ((((k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A))
% 0.68/0.86          = (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.68/0.86        | ~ (v1_relat_1 @ sk_A)
% 0.68/0.86        | ~ (v1_funct_1 @ sk_A)
% 0.68/0.86        | ~ (v2_funct_1 @ sk_A))),
% 0.68/0.86      inference('sup+', [status(thm)], ['94', '95'])).
% 0.68/0.86  thf('97', plain, ((v1_relat_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('98', plain, ((v1_funct_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('99', plain, ((v2_funct_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('100', plain,
% 0.68/0.86      (((k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A))
% 0.68/0.86         = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.68/0.86      inference('demod', [status(thm)], ['96', '97', '98', '99'])).
% 0.68/0.86  thf('101', plain,
% 0.68/0.86      (![X7 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X7)) = (k6_relat_1 @ X7))),
% 0.68/0.86      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.68/0.86  thf('102', plain,
% 0.68/0.86      (((k6_relat_1 @ (k1_relat_1 @ sk_A))
% 0.68/0.86         = (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A))))),
% 0.68/0.86      inference('demod', [status(thm)], ['93', '100', '101'])).
% 0.68/0.86  thf('103', plain,
% 0.68/0.86      (((k5_relat_1 @ sk_B @ (k6_relat_1 @ (k1_relat_1 @ sk_A))) = (sk_B))),
% 0.68/0.86      inference('demod', [status(thm)], ['30', '31'])).
% 0.68/0.86  thf('104', plain,
% 0.68/0.86      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('105', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.68/0.86  thf('106', plain,
% 0.68/0.86      (((sk_B)
% 0.68/0.86         = (k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ (k4_relat_1 @ sk_A)))),
% 0.68/0.86      inference('demod', [status(thm)], ['56', '102', '103', '104', '105'])).
% 0.68/0.86  thf('107', plain,
% 0.68/0.86      ((((sk_B)
% 0.68/0.86          = (k4_relat_1 @ (k5_relat_1 @ sk_A @ (k5_relat_1 @ sk_B @ sk_A))))
% 0.68/0.86        | ~ (v1_relat_1 @ sk_A))),
% 0.68/0.86      inference('sup+', [status(thm)], ['10', '106'])).
% 0.68/0.86  thf('108', plain,
% 0.68/0.86      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('109', plain,
% 0.68/0.86      (![X8 : $i]:
% 0.68/0.86         (((k5_relat_1 @ X8 @ (k6_relat_1 @ (k2_relat_1 @ X8))) = (X8))
% 0.68/0.86          | ~ (v1_relat_1 @ X8))),
% 0.68/0.86      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.68/0.86  thf('110', plain,
% 0.68/0.86      ((((k5_relat_1 @ sk_A @ (k5_relat_1 @ sk_B @ sk_A)) = (sk_A))
% 0.68/0.86        | ~ (v1_relat_1 @ sk_A))),
% 0.68/0.86      inference('sup+', [status(thm)], ['108', '109'])).
% 0.68/0.86  thf('111', plain, ((v1_relat_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('112', plain,
% 0.68/0.86      (((k5_relat_1 @ sk_A @ (k5_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['110', '111'])).
% 0.68/0.86  thf('113', plain, ((v1_relat_1 @ sk_A)),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('114', plain, (((sk_B) = (k4_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['107', '112', '113'])).
% 0.68/0.86  thf('115', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf('116', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.68/0.86  thf('117', plain, (((sk_B) != (k4_relat_1 @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['115', '116'])).
% 0.68/0.86  thf('118', plain, ($false),
% 0.68/0.86      inference('simplify_reflect-', [status(thm)], ['114', '117'])).
% 0.68/0.86  
% 0.68/0.86  % SZS output end Refutation
% 0.68/0.86  
% 0.68/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

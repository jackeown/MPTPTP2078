%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1QkFRldTEj

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:41 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 550 expanded)
%              Number of leaves         :   20 ( 173 expanded)
%              Depth                    :   19
%              Number of atoms          :  868 (8310 expanded)
%              Number of equality atoms :   72 ( 870 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X5 ) )
      = ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k5_relat_1 @ X14 @ ( k2_funct_1 @ X14 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

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

thf('8',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('9',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ X6 @ ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('10',plain,
    ( ( ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
        = ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
        = ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
        = ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
        = ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ sk_A @ X0 )
        = ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) )
      = ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('27',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('28',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_funct_1 @ sk_A )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('33',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k5_relat_1 @ X14 @ ( k2_funct_1 @ X14 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('34',plain,
    ( ( ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k5_relat_1 @ sk_A @ ( k4_relat_1 @ sk_A ) )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ X6 @ ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('41',plain,
    ( ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
      = sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('48',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('49',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('50',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) )
    = ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','31','38','43','44','45','46','47','53'])).

thf('55',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('56',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X14 ) @ X14 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('57',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
    = ( k5_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','59','60','61'])).

thf('63',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('66',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ sk_B )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['54','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ sk_B )
    = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ sk_B )
      = ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['5','70'])).

thf('72',plain,
    ( ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['10','11'])).

thf('73',plain,
    ( ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) )
    = ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','31','38','43','44','45','46','47','53'])).

thf('74',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) @ X0 )
        = ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) @ X0 )
        = ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) @ sk_A )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['72','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ sk_B )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['71','81','82'])).

thf('84',plain,
    ( ( ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ sk_B ) )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','83'])).

thf('85',plain,
    ( ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) )
    = ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','31','38','43','44','45','46','47','53'])).

thf('86',plain,
    ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['41','42'])).

thf('87',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( sk_B
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86','87','88','89'])).

thf('91',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('93',plain,(
    sk_B
 != ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['90','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1QkFRldTEj
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:08:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.46/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.68  % Solved by: fo/fo7.sh
% 0.46/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.68  % done 380 iterations in 0.233s
% 0.46/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.68  % SZS output start Refutation
% 0.46/0.68  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.68  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.68  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.46/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.68  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.46/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.68  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.68  thf(t55_relat_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( v1_relat_1 @ A ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( v1_relat_1 @ B ) =>
% 0.46/0.68           ( ![C:$i]:
% 0.46/0.68             ( ( v1_relat_1 @ C ) =>
% 0.46/0.68               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.46/0.68                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.46/0.68  thf('0', plain,
% 0.46/0.68      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.68         (~ (v1_relat_1 @ X2)
% 0.46/0.68          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 0.46/0.68              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 0.46/0.68          | ~ (v1_relat_1 @ X4)
% 0.46/0.68          | ~ (v1_relat_1 @ X3))),
% 0.46/0.68      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.46/0.68  thf(t72_relat_1, axiom,
% 0.46/0.68    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.46/0.68  thf('1', plain,
% 0.46/0.68      (![X5 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X5)) = (k6_relat_1 @ X5))),
% 0.46/0.68      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.46/0.68  thf(t54_relat_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( v1_relat_1 @ A ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( v1_relat_1 @ B ) =>
% 0.46/0.68           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.46/0.68             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.46/0.68  thf('2', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (v1_relat_1 @ X0)
% 0.46/0.68          | ((k4_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.46/0.68              = (k5_relat_1 @ (k4_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.46/0.68          | ~ (v1_relat_1 @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.46/0.68  thf('3', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.46/0.68            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.46/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.46/0.68          | ~ (v1_relat_1 @ X1))),
% 0.46/0.68      inference('sup+', [status(thm)], ['1', '2'])).
% 0.46/0.68  thf(fc3_funct_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.46/0.68       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.46/0.68  thf('4', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.46/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.68  thf('5', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.46/0.68            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.46/0.68          | ~ (v1_relat_1 @ X1))),
% 0.46/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.68  thf(t61_funct_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.68       ( ( v2_funct_1 @ A ) =>
% 0.46/0.68         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.46/0.68             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.46/0.68           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.46/0.68             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.46/0.68  thf('6', plain,
% 0.46/0.68      (![X14 : $i]:
% 0.46/0.68         (~ (v2_funct_1 @ X14)
% 0.46/0.68          | ((k5_relat_1 @ X14 @ (k2_funct_1 @ X14))
% 0.46/0.68              = (k6_relat_1 @ (k1_relat_1 @ X14)))
% 0.46/0.68          | ~ (v1_funct_1 @ X14)
% 0.46/0.68          | ~ (v1_relat_1 @ X14))),
% 0.46/0.68      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.46/0.68  thf('7', plain,
% 0.46/0.68      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.68         (~ (v1_relat_1 @ X2)
% 0.46/0.68          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 0.46/0.68              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 0.46/0.68          | ~ (v1_relat_1 @ X4)
% 0.46/0.68          | ~ (v1_relat_1 @ X3))),
% 0.46/0.68      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.46/0.68  thf(t64_funct_1, conjecture,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.68           ( ( ( v2_funct_1 @ A ) & 
% 0.46/0.68               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.46/0.68               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.46/0.68             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.46/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.68    (~( ![A:$i]:
% 0.46/0.68        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.68          ( ![B:$i]:
% 0.46/0.68            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.68              ( ( ( v2_funct_1 @ A ) & 
% 0.46/0.68                  ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.46/0.68                  ( ( k5_relat_1 @ B @ A ) =
% 0.46/0.68                    ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.46/0.68                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.46/0.68    inference('cnf.neg', [status(esa)], [t64_funct_1])).
% 0.46/0.68  thf('8', plain,
% 0.46/0.68      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(t80_relat_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( v1_relat_1 @ A ) =>
% 0.46/0.68       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.46/0.68  thf('9', plain,
% 0.46/0.68      (![X6 : $i]:
% 0.46/0.68         (((k5_relat_1 @ X6 @ (k6_relat_1 @ (k2_relat_1 @ X6))) = (X6))
% 0.46/0.68          | ~ (v1_relat_1 @ X6))),
% 0.46/0.68      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.46/0.68  thf('10', plain,
% 0.46/0.68      ((((k5_relat_1 @ sk_A @ (k5_relat_1 @ sk_B @ sk_A)) = (sk_A))
% 0.46/0.68        | ~ (v1_relat_1 @ sk_A))),
% 0.46/0.68      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.68  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('12', plain,
% 0.46/0.68      (((k5_relat_1 @ sk_A @ (k5_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['10', '11'])).
% 0.46/0.68  thf('13', plain,
% 0.46/0.68      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.68         (~ (v1_relat_1 @ X2)
% 0.46/0.68          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 0.46/0.68              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 0.46/0.68          | ~ (v1_relat_1 @ X4)
% 0.46/0.68          | ~ (v1_relat_1 @ X3))),
% 0.46/0.68      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.46/0.68  thf('14', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((k5_relat_1 @ sk_A @ X0)
% 0.46/0.68            = (k5_relat_1 @ sk_A @ 
% 0.46/0.68               (k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ X0)))
% 0.46/0.68          | ~ (v1_relat_1 @ sk_A)
% 0.46/0.68          | ~ (v1_relat_1 @ X0)
% 0.46/0.68          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['12', '13'])).
% 0.46/0.68  thf('15', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('16', plain,
% 0.46/0.68      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('17', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.46/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.68  thf('18', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A))),
% 0.46/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.46/0.68  thf('19', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((k5_relat_1 @ sk_A @ X0)
% 0.46/0.68            = (k5_relat_1 @ sk_A @ 
% 0.46/0.68               (k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ X0)))
% 0.46/0.68          | ~ (v1_relat_1 @ X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['14', '15', '18'])).
% 0.46/0.68  thf('20', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((k5_relat_1 @ sk_A @ X0)
% 0.46/0.68            = (k5_relat_1 @ sk_A @ 
% 0.46/0.68               (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ X0))))
% 0.46/0.68          | ~ (v1_relat_1 @ sk_B)
% 0.46/0.68          | ~ (v1_relat_1 @ X0)
% 0.46/0.68          | ~ (v1_relat_1 @ sk_A)
% 0.46/0.68          | ~ (v1_relat_1 @ X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['7', '19'])).
% 0.46/0.68  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('23', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((k5_relat_1 @ sk_A @ X0)
% 0.46/0.68            = (k5_relat_1 @ sk_A @ 
% 0.46/0.68               (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ X0))))
% 0.46/0.68          | ~ (v1_relat_1 @ X0)
% 0.46/0.68          | ~ (v1_relat_1 @ X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.46/0.68  thf('24', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (v1_relat_1 @ X0)
% 0.46/0.68          | ((k5_relat_1 @ sk_A @ X0)
% 0.46/0.68              = (k5_relat_1 @ sk_A @ 
% 0.46/0.68                 (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ X0)))))),
% 0.46/0.68      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.68  thf('25', plain,
% 0.46/0.68      ((((k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A))
% 0.46/0.68          = (k5_relat_1 @ sk_A @ 
% 0.46/0.68             (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))))
% 0.46/0.68        | ~ (v1_relat_1 @ sk_A)
% 0.46/0.68        | ~ (v1_funct_1 @ sk_A)
% 0.46/0.68        | ~ (v2_funct_1 @ sk_A)
% 0.46/0.68        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['6', '24'])).
% 0.46/0.68  thf('26', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(d9_funct_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.68       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.46/0.68  thf('27', plain,
% 0.46/0.68      (![X10 : $i]:
% 0.46/0.68         (~ (v2_funct_1 @ X10)
% 0.46/0.68          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.46/0.68          | ~ (v1_funct_1 @ X10)
% 0.46/0.68          | ~ (v1_relat_1 @ X10))),
% 0.46/0.68      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.46/0.68  thf('28', plain,
% 0.46/0.68      ((~ (v1_funct_1 @ sk_A)
% 0.46/0.68        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))
% 0.46/0.68        | ~ (v2_funct_1 @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.68  thf('29', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('30', plain, ((v2_funct_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('31', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.46/0.68  thf('32', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.46/0.68  thf('33', plain,
% 0.46/0.68      (![X14 : $i]:
% 0.46/0.68         (~ (v2_funct_1 @ X14)
% 0.46/0.68          | ((k5_relat_1 @ X14 @ (k2_funct_1 @ X14))
% 0.46/0.68              = (k6_relat_1 @ (k1_relat_1 @ X14)))
% 0.46/0.68          | ~ (v1_funct_1 @ X14)
% 0.46/0.68          | ~ (v1_relat_1 @ X14))),
% 0.46/0.68      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.46/0.68  thf('34', plain,
% 0.46/0.68      ((((k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A))
% 0.46/0.68          = (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 0.46/0.68        | ~ (v1_relat_1 @ sk_A)
% 0.46/0.68        | ~ (v1_funct_1 @ sk_A)
% 0.46/0.68        | ~ (v2_funct_1 @ sk_A))),
% 0.46/0.68      inference('sup+', [status(thm)], ['32', '33'])).
% 0.46/0.68  thf('35', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('36', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('37', plain, ((v2_funct_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('38', plain,
% 0.46/0.68      (((k5_relat_1 @ sk_A @ (k4_relat_1 @ sk_A))
% 0.46/0.68         = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.46/0.68      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.46/0.68  thf('39', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('40', plain,
% 0.46/0.68      (![X6 : $i]:
% 0.46/0.68         (((k5_relat_1 @ X6 @ (k6_relat_1 @ (k2_relat_1 @ X6))) = (X6))
% 0.46/0.68          | ~ (v1_relat_1 @ X6))),
% 0.46/0.68      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.46/0.68  thf('41', plain,
% 0.46/0.68      ((((k5_relat_1 @ sk_B @ (k6_relat_1 @ (k1_relat_1 @ sk_A))) = (sk_B))
% 0.46/0.68        | ~ (v1_relat_1 @ sk_B))),
% 0.46/0.68      inference('sup+', [status(thm)], ['39', '40'])).
% 0.46/0.68  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('43', plain,
% 0.46/0.68      (((k5_relat_1 @ sk_B @ (k6_relat_1 @ (k1_relat_1 @ sk_A))) = (sk_B))),
% 0.46/0.68      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.68  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('45', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('46', plain, ((v2_funct_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('47', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.46/0.68  thf('48', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.46/0.68  thf(dt_k2_funct_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.68       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.46/0.68         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.46/0.68  thf('49', plain,
% 0.46/0.68      (![X11 : $i]:
% 0.46/0.68         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 0.46/0.68          | ~ (v1_funct_1 @ X11)
% 0.46/0.68          | ~ (v1_relat_1 @ X11))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.68  thf('50', plain,
% 0.46/0.68      (((v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.46/0.68        | ~ (v1_relat_1 @ sk_A)
% 0.46/0.68        | ~ (v1_funct_1 @ sk_A))),
% 0.46/0.68      inference('sup+', [status(thm)], ['48', '49'])).
% 0.46/0.68  thf('51', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('52', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('53', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.46/0.68  thf('54', plain,
% 0.46/0.68      (((k6_relat_1 @ (k1_relat_1 @ sk_A)) = (k5_relat_1 @ sk_A @ sk_B))),
% 0.46/0.68      inference('demod', [status(thm)],
% 0.46/0.68                ['25', '31', '38', '43', '44', '45', '46', '47', '53'])).
% 0.46/0.68  thf('55', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.46/0.68  thf('56', plain,
% 0.46/0.68      (![X14 : $i]:
% 0.46/0.68         (~ (v2_funct_1 @ X14)
% 0.46/0.68          | ((k5_relat_1 @ (k2_funct_1 @ X14) @ X14)
% 0.46/0.68              = (k6_relat_1 @ (k2_relat_1 @ X14)))
% 0.46/0.68          | ~ (v1_funct_1 @ X14)
% 0.46/0.68          | ~ (v1_relat_1 @ X14))),
% 0.46/0.68      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.46/0.68  thf('57', plain,
% 0.46/0.68      ((((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 0.46/0.68          = (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 0.46/0.68        | ~ (v1_relat_1 @ sk_A)
% 0.46/0.68        | ~ (v1_funct_1 @ sk_A)
% 0.46/0.68        | ~ (v2_funct_1 @ sk_A))),
% 0.46/0.68      inference('sup+', [status(thm)], ['55', '56'])).
% 0.46/0.68  thf('58', plain,
% 0.46/0.68      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('59', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('60', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('61', plain, ((v2_funct_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('62', plain,
% 0.46/0.68      (((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A) = (k5_relat_1 @ sk_B @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['57', '58', '59', '60', '61'])).
% 0.46/0.68  thf('63', plain,
% 0.46/0.68      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.68         (~ (v1_relat_1 @ X2)
% 0.46/0.68          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 0.46/0.68              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 0.46/0.68          | ~ (v1_relat_1 @ X4)
% 0.46/0.68          | ~ (v1_relat_1 @ X3))),
% 0.46/0.68      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.46/0.68  thf('64', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ X0)
% 0.46/0.68            = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 0.46/0.68          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.46/0.68          | ~ (v1_relat_1 @ X0)
% 0.46/0.68          | ~ (v1_relat_1 @ sk_A))),
% 0.46/0.68      inference('sup+', [status(thm)], ['62', '63'])).
% 0.46/0.68  thf('65', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.46/0.68  thf('66', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('67', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ X0)
% 0.46/0.68            = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 0.46/0.68          | ~ (v1_relat_1 @ X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.46/0.68  thf('68', plain,
% 0.46/0.68      ((((k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ sk_B)
% 0.46/0.68          = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ 
% 0.46/0.68             (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 0.46/0.68        | ~ (v1_relat_1 @ sk_B))),
% 0.46/0.68      inference('sup+', [status(thm)], ['54', '67'])).
% 0.46/0.68  thf('69', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('70', plain,
% 0.46/0.68      (((k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ sk_B)
% 0.46/0.68         = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ 
% 0.46/0.68            (k6_relat_1 @ (k1_relat_1 @ sk_A))))),
% 0.46/0.68      inference('demod', [status(thm)], ['68', '69'])).
% 0.46/0.68  thf('71', plain,
% 0.46/0.68      ((((k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ sk_B)
% 0.46/0.68          = (k4_relat_1 @ 
% 0.46/0.68             (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)) @ sk_A)))
% 0.46/0.68        | ~ (v1_relat_1 @ sk_A))),
% 0.46/0.68      inference('sup+', [status(thm)], ['5', '70'])).
% 0.46/0.68  thf('72', plain,
% 0.46/0.68      (((k5_relat_1 @ sk_A @ (k5_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['10', '11'])).
% 0.46/0.68  thf('73', plain,
% 0.46/0.68      (((k6_relat_1 @ (k1_relat_1 @ sk_A)) = (k5_relat_1 @ sk_A @ sk_B))),
% 0.46/0.68      inference('demod', [status(thm)],
% 0.46/0.68                ['25', '31', '38', '43', '44', '45', '46', '47', '53'])).
% 0.46/0.68  thf('74', plain,
% 0.46/0.68      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.68         (~ (v1_relat_1 @ X2)
% 0.46/0.68          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 0.46/0.68              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 0.46/0.68          | ~ (v1_relat_1 @ X4)
% 0.46/0.68          | ~ (v1_relat_1 @ X3))),
% 0.46/0.68      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.46/0.68  thf('75', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)) @ X0)
% 0.46/0.68            = (k5_relat_1 @ sk_A @ (k5_relat_1 @ sk_B @ X0)))
% 0.46/0.68          | ~ (v1_relat_1 @ sk_A)
% 0.46/0.68          | ~ (v1_relat_1 @ X0)
% 0.46/0.68          | ~ (v1_relat_1 @ sk_B))),
% 0.46/0.68      inference('sup+', [status(thm)], ['73', '74'])).
% 0.46/0.68  thf('76', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('77', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('78', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)) @ X0)
% 0.46/0.68            = (k5_relat_1 @ sk_A @ (k5_relat_1 @ sk_B @ X0)))
% 0.46/0.68          | ~ (v1_relat_1 @ X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.46/0.68  thf('79', plain,
% 0.46/0.68      ((((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)) @ sk_A) = (sk_A))
% 0.46/0.68        | ~ (v1_relat_1 @ sk_A))),
% 0.46/0.68      inference('sup+', [status(thm)], ['72', '78'])).
% 0.46/0.68  thf('80', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('81', plain,
% 0.46/0.68      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)) @ sk_A) = (sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['79', '80'])).
% 0.46/0.68  thf('82', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('83', plain,
% 0.46/0.68      (((k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ sk_B) = (k4_relat_1 @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['71', '81', '82'])).
% 0.46/0.68  thf('84', plain,
% 0.46/0.68      ((((k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ sk_B)) = (k4_relat_1 @ sk_A))
% 0.46/0.68        | ~ (v1_relat_1 @ sk_B)
% 0.46/0.68        | ~ (v1_relat_1 @ sk_B)
% 0.46/0.68        | ~ (v1_relat_1 @ sk_A))),
% 0.46/0.68      inference('sup+', [status(thm)], ['0', '83'])).
% 0.46/0.68  thf('85', plain,
% 0.46/0.68      (((k6_relat_1 @ (k1_relat_1 @ sk_A)) = (k5_relat_1 @ sk_A @ sk_B))),
% 0.46/0.68      inference('demod', [status(thm)],
% 0.46/0.68                ['25', '31', '38', '43', '44', '45', '46', '47', '53'])).
% 0.46/0.68  thf('86', plain,
% 0.46/0.68      (((k5_relat_1 @ sk_B @ (k6_relat_1 @ (k1_relat_1 @ sk_A))) = (sk_B))),
% 0.46/0.68      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.68  thf('87', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('88', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('89', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('90', plain, (((sk_B) = (k4_relat_1 @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['84', '85', '86', '87', '88', '89'])).
% 0.46/0.68  thf('91', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('92', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.46/0.68  thf('93', plain, (((sk_B) != (k4_relat_1 @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['91', '92'])).
% 0.46/0.68  thf('94', plain, ($false),
% 0.46/0.68      inference('simplify_reflect-', [status(thm)], ['90', '93'])).
% 0.46/0.68  
% 0.46/0.68  % SZS output end Refutation
% 0.46/0.68  
% 0.46/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

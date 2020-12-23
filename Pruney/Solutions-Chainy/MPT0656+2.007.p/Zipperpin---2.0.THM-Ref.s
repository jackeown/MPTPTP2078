%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w5UsyDx9Ah

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 186 expanded)
%              Number of leaves         :   24 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  763 (2457 expanded)
%              Number of equality atoms :   67 ( 259 expanded)
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

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t63_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
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
                & ( ( k2_relat_1 @ A )
                  = ( k1_relat_1 @ B ) )
                & ( ( k5_relat_1 @ A @ B )
                  = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
             => ( B
                = ( k2_funct_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_funct_1])).

thf('0',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
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
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ X11 )
        = ( k4_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_funct_1 @ sk_A )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('16',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

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
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('25',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('26',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','29','30'])).

thf('32',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
      = ( k4_relat_1 @ ( k5_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','31'])).

thf('33',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('34',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('35',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['33','34'])).

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

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X16 ) )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('37',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38','39','40','41','42'])).

thf('44',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['43'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X9 ) @ X8 )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('51',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ X10 @ ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X16 ) )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
       != ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('58',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('59',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('60',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('61',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('62',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('63',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('64',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57','58','59','60','61','62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X9 ) @ X8 )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k5_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_A )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['49','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k5_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( sk_B
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['32','48','71','72','73'])).

thf('75',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('77',plain,(
    sk_B
 != ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['74','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w5UsyDx9Ah
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:37:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 179 iterations in 0.089s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.20/0.50  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.50  thf(t63_funct_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50           ( ( ( v2_funct_1 @ A ) & 
% 0.20/0.50               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.20/0.50               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.20/0.50             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50              ( ( ( v2_funct_1 @ A ) & 
% 0.20/0.50                  ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.20/0.50                  ( ( k5_relat_1 @ A @ B ) =
% 0.20/0.50                    ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.20/0.50                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t63_funct_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t72_relat_1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X7 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X7)) = (k6_relat_1 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.20/0.50  thf(t54_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( v1_relat_1 @ B ) =>
% 0.20/0.50           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.20/0.50             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | ((k4_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.20/0.50              = (k5_relat_1 @ (k4_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.20/0.50          | ~ (v1_relat_1 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.20/0.50            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.50          | ~ (v1_relat_1 @ X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf(fc3_funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.50  thf('4', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.20/0.50            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ X1))),
% 0.20/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)) @ X0))
% 0.20/0.50            = (k5_relat_1 @ (k4_relat_1 @ X0) @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.20/0.50          | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['0', '5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k4_relat_1 @ (k5_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ X0))
% 0.20/0.50            = (k5_relat_1 @ (k4_relat_1 @ X0) @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.20/0.50          | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d9_funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.50       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X11 : $i]:
% 0.20/0.50         (~ (v2_funct_1 @ X11)
% 0.20/0.50          | ((k2_funct_1 @ X11) = (k4_relat_1 @ X11))
% 0.20/0.50          | ~ (v1_funct_1 @ X11)
% 0.20/0.50          | ~ (v1_relat_1 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      ((~ (v1_funct_1 @ sk_A)
% 0.20/0.50        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))
% 0.20/0.50        | ~ (v2_funct_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('12', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('13', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('14', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.50  thf(t61_funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.50       ( ( v2_funct_1 @ A ) =>
% 0.20/0.50         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.20/0.50             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.20/0.50           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.20/0.50             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X17 : $i]:
% 0.20/0.50         (~ (v2_funct_1 @ X17)
% 0.20/0.50          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 0.20/0.50              = (k6_relat_1 @ (k2_relat_1 @ X17)))
% 0.20/0.50          | ~ (v1_funct_1 @ X17)
% 0.20/0.50          | ~ (v1_relat_1 @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      ((((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 0.20/0.50          = (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_A)
% 0.20/0.50        | ~ (v1_funct_1 @ sk_A)
% 0.20/0.50        | ~ (v2_funct_1 @ sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('19', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('20', plain, ((v2_funct_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 0.20/0.50         = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.20/0.50  thf(t55_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( v1_relat_1 @ B ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( v1_relat_1 @ C ) =>
% 0.20/0.50               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.20/0.50                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X2)
% 0.20/0.50          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 0.20/0.50              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 0.20/0.50          | ~ (v1_relat_1 @ X4)
% 0.20/0.50          | ~ (v1_relat_1 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.20/0.50            = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.50  thf(dt_k2_funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.50       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.20/0.50         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X12 : $i]:
% 0.20/0.50         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 0.20/0.50          | ~ (v1_funct_1 @ X12)
% 0.20/0.50          | ~ (v1_relat_1 @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (((v1_relat_1 @ (k4_relat_1 @ sk_A))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_A)
% 0.20/0.50        | ~ (v1_funct_1 @ sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('28', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('29', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.20/0.50  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.20/0.50            = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['23', '29', '30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      ((((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B)
% 0.20/0.50          = (k4_relat_1 @ (k5_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_A)))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_A)
% 0.20/0.50        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.50      inference('sup+', [status(thm)], ['8', '31'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t71_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.50       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.50  thf('34', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) = (k1_relat_1 @ sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf(t27_funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 0.20/0.50             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X15)
% 0.20/0.50          | ~ (v1_funct_1 @ X15)
% 0.20/0.50          | (r1_tarski @ (k2_relat_1 @ X15) @ (k1_relat_1 @ X16))
% 0.20/0.50          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X16)) != (k1_relat_1 @ X15))
% 0.20/0.50          | ~ (v1_funct_1 @ X16)
% 0.20/0.50          | ~ (v1_relat_1 @ X16))),
% 0.20/0.50      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.50        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.50        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.20/0.50        | ~ (v1_funct_1 @ sk_A)
% 0.20/0.50        | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('39', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('40', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('41', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('42', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.20/0.50        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['37', '38', '39', '40', '41', '42'])).
% 0.20/0.50  thf('44', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.20/0.50      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.50  thf(t77_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.20/0.50         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.20/0.50          | ((k5_relat_1 @ (k6_relat_1 @ X9) @ X8) = (X8))
% 0.20/0.50          | ~ (v1_relat_1 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.50        | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B) = (sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.50  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B) = (sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('50', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.50  thf(t80_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (![X10 : $i]:
% 0.20/0.50         (((k5_relat_1 @ X10 @ (k6_relat_1 @ (k2_relat_1 @ X10))) = (X10))
% 0.20/0.50          | ~ (v1_relat_1 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.20/0.50            = (k6_relat_1 @ X0))
% 0.20/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['50', '51'])).
% 0.20/0.50  thf('53', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.20/0.50           = (k6_relat_1 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X15)
% 0.20/0.50          | ~ (v1_funct_1 @ X15)
% 0.20/0.50          | (r1_tarski @ (k2_relat_1 @ X15) @ (k1_relat_1 @ X16))
% 0.20/0.50          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X16)) != (k1_relat_1 @ X15))
% 0.20/0.50          | ~ (v1_funct_1 @ X16)
% 0.20/0.50          | ~ (v1_relat_1 @ X16))),
% 0.20/0.50      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k1_relat_1 @ (k6_relat_1 @ X0)) != (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.50          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.20/0.50          | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.20/0.50             (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.50          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.20/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.50  thf('57', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.50  thf('58', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.50  thf('59', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.50  thf('60', plain, (![X14 : $i]: (v1_funct_1 @ (k6_relat_1 @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.50  thf('61', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.50  thf('62', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.50  thf('63', plain, (![X14 : $i]: (v1_funct_1 @ (k6_relat_1 @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.50  thf('64', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.50  thf('65', plain, (![X0 : $i]: (((X0) != (X0)) | (r1_tarski @ X0 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)],
% 0.20/0.50                ['56', '57', '58', '59', '60', '61', '62', '63', '64'])).
% 0.20/0.50  thf('66', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.50      inference('simplify', [status(thm)], ['65'])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.20/0.50          | ((k5_relat_1 @ (k6_relat_1 @ X9) @ X8) = (X8))
% 0.20/0.50          | ~ (v1_relat_1 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.50  thf('69', plain,
% 0.20/0.50      ((((k5_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_A) = (sk_A))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.50      inference('sup+', [status(thm)], ['49', '68'])).
% 0.20/0.50  thf('70', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('71', plain,
% 0.20/0.50      (((k5_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_A) = (sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['69', '70'])).
% 0.20/0.50  thf('72', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('73', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('74', plain, (((sk_B) = (k4_relat_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['32', '48', '71', '72', '73'])).
% 0.20/0.50  thf('75', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('76', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.50  thf('77', plain, (((sk_B) != (k4_relat_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['75', '76'])).
% 0.20/0.50  thf('78', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['74', '77'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

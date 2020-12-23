%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CYF2pmotem

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:43 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 355 expanded)
%              Number of leaves         :   18 ( 115 expanded)
%              Depth                    :   24
%              Number of atoms          : 1307 (5412 expanded)
%              Number of equality atoms :   88 ( 515 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) @ X3 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
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

thf('2',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

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

thf('3',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) @ X3 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('5',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ sk_A )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['5','6'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','12'])).

thf('14',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['1','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) )
    = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) @ X3 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('24',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('25',plain,
    ( ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) )
    = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('26',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) @ X3 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ) @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['25','31'])).

thf('33',plain,
    ( ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) )
    = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('34',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('35',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('36',plain,
    ( ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) )
    = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ) @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,
    ( ( ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['24','36'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) )
    = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,
    ( ( ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['23','42'])).

thf('44',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('45',plain,
    ( ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) )
    = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','45'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('47',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('48',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('49',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['46','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('62',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['60','61'])).

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

thf('63',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ( v2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['64','65','66','67','68','69'])).

thf('71',plain,(
    v2_funct_1 @ sk_B ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58','59','71'])).

thf('73',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('74',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
      = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['72','79'])).

thf('81',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('82',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('84',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('86',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('87',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) @ X3 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ ( k2_funct_1 @ sk_A ) )
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['84','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) @ ( k2_funct_1 @ sk_A ) )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,
    ( ( ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['83','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
      = ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ ( k2_funct_1 @ sk_A ) ) )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['81','103'])).

thf('105',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_funct_1 @ sk_B ),
    inference(simplify,[status(thm)],['70'])).

thf('113',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['80','109','110','111','112','113'])).

thf('115',plain,
    ( ( sk_B
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( sk_B
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['117','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CYF2pmotem
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:47:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.32/1.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.32/1.53  % Solved by: fo/fo7.sh
% 1.32/1.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.32/1.53  % done 361 iterations in 1.081s
% 1.32/1.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.32/1.53  % SZS output start Refutation
% 1.32/1.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.32/1.53  thf(sk_A_type, type, sk_A: $i).
% 1.32/1.53  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.32/1.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.32/1.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.32/1.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.32/1.53  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.32/1.53  thf(sk_B_type, type, sk_B: $i).
% 1.32/1.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.32/1.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.32/1.53  thf(t78_relat_1, axiom,
% 1.32/1.53    (![A:$i]:
% 1.32/1.53     ( ( v1_relat_1 @ A ) =>
% 1.32/1.53       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 1.32/1.53  thf('0', plain,
% 1.32/1.53      (![X3 : $i]:
% 1.32/1.53         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X3)) @ X3) = (X3))
% 1.32/1.53          | ~ (v1_relat_1 @ X3))),
% 1.32/1.53      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.32/1.53  thf(dt_k2_funct_1, axiom,
% 1.32/1.53    (![A:$i]:
% 1.32/1.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.32/1.53       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.32/1.53         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.32/1.53  thf('1', plain,
% 1.32/1.53      (![X4 : $i]:
% 1.32/1.53         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 1.32/1.53          | ~ (v1_funct_1 @ X4)
% 1.32/1.53          | ~ (v1_relat_1 @ X4))),
% 1.32/1.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.32/1.53  thf(t61_funct_1, axiom,
% 1.32/1.53    (![A:$i]:
% 1.32/1.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.32/1.53       ( ( v2_funct_1 @ A ) =>
% 1.32/1.53         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.32/1.53             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.32/1.53           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.32/1.53             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.32/1.53  thf('2', plain,
% 1.32/1.53      (![X10 : $i]:
% 1.32/1.53         (~ (v2_funct_1 @ X10)
% 1.32/1.53          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 1.32/1.53              = (k6_relat_1 @ (k1_relat_1 @ X10)))
% 1.32/1.53          | ~ (v1_funct_1 @ X10)
% 1.32/1.53          | ~ (v1_relat_1 @ X10))),
% 1.32/1.53      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.32/1.53  thf(t64_funct_1, conjecture,
% 1.32/1.53    (![A:$i]:
% 1.32/1.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.32/1.53       ( ![B:$i]:
% 1.32/1.53         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.32/1.53           ( ( ( v2_funct_1 @ A ) & 
% 1.32/1.53               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.32/1.53               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.32/1.53             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.32/1.53  thf(zf_stmt_0, negated_conjecture,
% 1.32/1.53    (~( ![A:$i]:
% 1.32/1.53        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.32/1.53          ( ![B:$i]:
% 1.32/1.53            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.32/1.53              ( ( ( v2_funct_1 @ A ) & 
% 1.32/1.53                  ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.32/1.53                  ( ( k5_relat_1 @ B @ A ) =
% 1.32/1.53                    ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.32/1.53                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 1.32/1.53    inference('cnf.neg', [status(esa)], [t64_funct_1])).
% 1.32/1.53  thf('3', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('4', plain,
% 1.32/1.53      (![X3 : $i]:
% 1.32/1.53         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X3)) @ X3) = (X3))
% 1.32/1.53          | ~ (v1_relat_1 @ X3))),
% 1.32/1.53      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.32/1.53  thf('5', plain,
% 1.32/1.53      ((((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ sk_A) = (sk_A))
% 1.32/1.53        | ~ (v1_relat_1 @ sk_A))),
% 1.32/1.53      inference('sup+', [status(thm)], ['3', '4'])).
% 1.32/1.53  thf('6', plain, ((v1_relat_1 @ sk_A)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('7', plain,
% 1.32/1.53      (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ sk_A) = (sk_A))),
% 1.32/1.53      inference('demod', [status(thm)], ['5', '6'])).
% 1.32/1.53  thf(t55_relat_1, axiom,
% 1.32/1.53    (![A:$i]:
% 1.32/1.53     ( ( v1_relat_1 @ A ) =>
% 1.32/1.53       ( ![B:$i]:
% 1.32/1.53         ( ( v1_relat_1 @ B ) =>
% 1.32/1.53           ( ![C:$i]:
% 1.32/1.53             ( ( v1_relat_1 @ C ) =>
% 1.32/1.53               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.32/1.53                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.32/1.53  thf('8', plain,
% 1.32/1.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.53         (~ (v1_relat_1 @ X0)
% 1.32/1.53          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 1.32/1.53              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 1.32/1.53          | ~ (v1_relat_1 @ X2)
% 1.32/1.53          | ~ (v1_relat_1 @ X1))),
% 1.32/1.53      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.32/1.53  thf('9', plain,
% 1.32/1.53      (![X0 : $i]:
% 1.32/1.53         (((k5_relat_1 @ sk_A @ X0)
% 1.32/1.53            = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 1.32/1.53               (k5_relat_1 @ sk_A @ X0)))
% 1.32/1.53          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 1.32/1.53          | ~ (v1_relat_1 @ X0)
% 1.32/1.53          | ~ (v1_relat_1 @ sk_A))),
% 1.32/1.53      inference('sup+', [status(thm)], ['7', '8'])).
% 1.32/1.53  thf(fc4_funct_1, axiom,
% 1.32/1.53    (![A:$i]:
% 1.32/1.53     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.32/1.53       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.32/1.53  thf('10', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 1.32/1.53      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.32/1.53  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('12', plain,
% 1.32/1.53      (![X0 : $i]:
% 1.32/1.53         (((k5_relat_1 @ sk_A @ X0)
% 1.32/1.53            = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 1.32/1.53               (k5_relat_1 @ sk_A @ X0)))
% 1.32/1.53          | ~ (v1_relat_1 @ X0))),
% 1.32/1.53      inference('demod', [status(thm)], ['9', '10', '11'])).
% 1.32/1.53  thf('13', plain,
% 1.32/1.53      ((((k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A))
% 1.32/1.53          = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 1.32/1.53             (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 1.32/1.53        | ~ (v1_relat_1 @ sk_A)
% 1.32/1.53        | ~ (v1_funct_1 @ sk_A)
% 1.32/1.53        | ~ (v2_funct_1 @ sk_A)
% 1.32/1.53        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 1.32/1.53      inference('sup+', [status(thm)], ['2', '12'])).
% 1.32/1.53  thf('14', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('15', plain, ((v1_relat_1 @ sk_A)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('16', plain, ((v1_funct_1 @ sk_A)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('17', plain, ((v2_funct_1 @ sk_A)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('18', plain,
% 1.32/1.53      ((((k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A))
% 1.32/1.53          = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 1.32/1.53             (k6_relat_1 @ (k2_relat_1 @ sk_B))))
% 1.32/1.53        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 1.32/1.53      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 1.32/1.53  thf('19', plain,
% 1.32/1.53      ((~ (v1_relat_1 @ sk_A)
% 1.32/1.53        | ~ (v1_funct_1 @ sk_A)
% 1.32/1.53        | ((k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A))
% 1.32/1.53            = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 1.32/1.53               (k6_relat_1 @ (k2_relat_1 @ sk_B)))))),
% 1.32/1.53      inference('sup-', [status(thm)], ['1', '18'])).
% 1.32/1.53  thf('20', plain, ((v1_relat_1 @ sk_A)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('21', plain, ((v1_funct_1 @ sk_A)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('22', plain,
% 1.32/1.53      (((k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A))
% 1.32/1.53         = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 1.32/1.53            (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 1.32/1.53      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.32/1.53  thf('23', plain,
% 1.32/1.53      (![X3 : $i]:
% 1.32/1.53         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X3)) @ X3) = (X3))
% 1.32/1.53          | ~ (v1_relat_1 @ X3))),
% 1.32/1.53      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.32/1.53  thf('24', plain,
% 1.32/1.53      (![X10 : $i]:
% 1.32/1.53         (~ (v2_funct_1 @ X10)
% 1.32/1.53          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 1.32/1.53              = (k6_relat_1 @ (k1_relat_1 @ X10)))
% 1.32/1.53          | ~ (v1_funct_1 @ X10)
% 1.32/1.53          | ~ (v1_relat_1 @ X10))),
% 1.32/1.53      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.32/1.53  thf('25', plain,
% 1.32/1.53      (((k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A))
% 1.32/1.53         = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 1.32/1.53            (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 1.32/1.53      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.32/1.53  thf('26', plain,
% 1.32/1.53      (![X3 : $i]:
% 1.32/1.53         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X3)) @ X3) = (X3))
% 1.32/1.53          | ~ (v1_relat_1 @ X3))),
% 1.32/1.53      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.32/1.53  thf('27', plain,
% 1.32/1.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.53         (~ (v1_relat_1 @ X0)
% 1.32/1.53          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 1.32/1.53              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 1.32/1.53          | ~ (v1_relat_1 @ X2)
% 1.32/1.53          | ~ (v1_relat_1 @ X1))),
% 1.32/1.53      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.32/1.53  thf('28', plain,
% 1.32/1.53      (![X0 : $i, X1 : $i]:
% 1.32/1.53         (((k5_relat_1 @ X0 @ X1)
% 1.32/1.53            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.32/1.53               (k5_relat_1 @ X0 @ X1)))
% 1.32/1.53          | ~ (v1_relat_1 @ X0)
% 1.32/1.53          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.32/1.53          | ~ (v1_relat_1 @ X1)
% 1.32/1.53          | ~ (v1_relat_1 @ X0))),
% 1.32/1.53      inference('sup+', [status(thm)], ['26', '27'])).
% 1.32/1.53  thf('29', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 1.32/1.53      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.32/1.53  thf('30', plain,
% 1.32/1.53      (![X0 : $i, X1 : $i]:
% 1.32/1.53         (((k5_relat_1 @ X0 @ X1)
% 1.32/1.53            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.32/1.53               (k5_relat_1 @ X0 @ X1)))
% 1.32/1.53          | ~ (v1_relat_1 @ X0)
% 1.32/1.53          | ~ (v1_relat_1 @ X1)
% 1.32/1.53          | ~ (v1_relat_1 @ X0))),
% 1.32/1.53      inference('demod', [status(thm)], ['28', '29'])).
% 1.32/1.53  thf('31', plain,
% 1.32/1.53      (![X0 : $i, X1 : $i]:
% 1.32/1.53         (~ (v1_relat_1 @ X1)
% 1.32/1.53          | ~ (v1_relat_1 @ X0)
% 1.32/1.53          | ((k5_relat_1 @ X0 @ X1)
% 1.32/1.53              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.32/1.53                 (k5_relat_1 @ X0 @ X1))))),
% 1.32/1.53      inference('simplify', [status(thm)], ['30'])).
% 1.32/1.53  thf('32', plain,
% 1.32/1.53      ((((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 1.32/1.53          (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 1.32/1.53          = (k5_relat_1 @ 
% 1.32/1.53             (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))) @ 
% 1.32/1.53             (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A))))
% 1.32/1.53        | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 1.32/1.53        | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 1.32/1.53      inference('sup+', [status(thm)], ['25', '31'])).
% 1.32/1.53  thf('33', plain,
% 1.32/1.53      (((k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A))
% 1.32/1.53         = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 1.32/1.53            (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 1.32/1.53      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.32/1.53  thf('34', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 1.32/1.53      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.32/1.53  thf('35', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 1.32/1.53      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.32/1.53  thf('36', plain,
% 1.32/1.53      (((k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A))
% 1.32/1.53         = (k5_relat_1 @ 
% 1.32/1.53            (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))) @ 
% 1.32/1.53            (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A))))),
% 1.32/1.53      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 1.32/1.53  thf('37', plain,
% 1.32/1.53      ((((k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A))
% 1.32/1.53          = (k5_relat_1 @ 
% 1.32/1.53             (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))) @ 
% 1.32/1.53             (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 1.32/1.53        | ~ (v1_relat_1 @ sk_A)
% 1.32/1.53        | ~ (v1_funct_1 @ sk_A)
% 1.32/1.53        | ~ (v2_funct_1 @ sk_A))),
% 1.32/1.53      inference('sup+', [status(thm)], ['24', '36'])).
% 1.32/1.53  thf('38', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('39', plain, ((v1_relat_1 @ sk_A)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('40', plain, ((v1_funct_1 @ sk_A)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('41', plain, ((v2_funct_1 @ sk_A)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('42', plain,
% 1.32/1.53      (((k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A))
% 1.32/1.53         = (k5_relat_1 @ 
% 1.32/1.53            (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))) @ 
% 1.32/1.53            (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 1.32/1.53      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 1.32/1.53  thf('43', plain,
% 1.32/1.53      ((((k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A))
% 1.32/1.53          = (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 1.32/1.53        | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 1.32/1.53      inference('sup+', [status(thm)], ['23', '42'])).
% 1.32/1.53  thf('44', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 1.32/1.53      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.32/1.53  thf('45', plain,
% 1.32/1.53      (((k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A))
% 1.32/1.53         = (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 1.32/1.53      inference('demod', [status(thm)], ['43', '44'])).
% 1.32/1.53  thf('46', plain,
% 1.32/1.53      (((k6_relat_1 @ (k2_relat_1 @ sk_B))
% 1.32/1.53         = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 1.32/1.53            (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 1.32/1.53      inference('demod', [status(thm)], ['22', '45'])).
% 1.32/1.53  thf(t55_funct_1, axiom,
% 1.32/1.53    (![A:$i]:
% 1.32/1.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.32/1.53       ( ( v2_funct_1 @ A ) =>
% 1.32/1.53         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.32/1.53           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.32/1.53  thf('47', plain,
% 1.32/1.53      (![X9 : $i]:
% 1.32/1.53         (~ (v2_funct_1 @ X9)
% 1.32/1.53          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 1.32/1.53          | ~ (v1_funct_1 @ X9)
% 1.32/1.53          | ~ (v1_relat_1 @ X9))),
% 1.32/1.53      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.32/1.53  thf('48', plain,
% 1.32/1.53      (![X4 : $i]:
% 1.32/1.53         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 1.32/1.53          | ~ (v1_funct_1 @ X4)
% 1.32/1.53          | ~ (v1_relat_1 @ X4))),
% 1.32/1.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.32/1.53  thf('49', plain,
% 1.32/1.53      (![X10 : $i]:
% 1.32/1.53         (~ (v2_funct_1 @ X10)
% 1.32/1.53          | ((k5_relat_1 @ (k2_funct_1 @ X10) @ X10)
% 1.32/1.53              = (k6_relat_1 @ (k2_relat_1 @ X10)))
% 1.32/1.53          | ~ (v1_funct_1 @ X10)
% 1.32/1.53          | ~ (v1_relat_1 @ X10))),
% 1.32/1.53      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.32/1.53  thf('50', plain,
% 1.32/1.53      (![X0 : $i, X1 : $i]:
% 1.32/1.53         (~ (v1_relat_1 @ X1)
% 1.32/1.53          | ~ (v1_relat_1 @ X0)
% 1.32/1.53          | ((k5_relat_1 @ X0 @ X1)
% 1.32/1.53              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.32/1.53                 (k5_relat_1 @ X0 @ X1))))),
% 1.32/1.53      inference('simplify', [status(thm)], ['30'])).
% 1.32/1.53  thf('51', plain,
% 1.32/1.53      (![X0 : $i]:
% 1.32/1.53         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.32/1.53            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 1.32/1.53               (k6_relat_1 @ (k2_relat_1 @ X0))))
% 1.32/1.53          | ~ (v1_relat_1 @ X0)
% 1.32/1.53          | ~ (v1_funct_1 @ X0)
% 1.32/1.53          | ~ (v2_funct_1 @ X0)
% 1.32/1.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.32/1.53          | ~ (v1_relat_1 @ X0))),
% 1.32/1.53      inference('sup+', [status(thm)], ['49', '50'])).
% 1.32/1.53  thf('52', plain,
% 1.32/1.53      (![X0 : $i]:
% 1.32/1.53         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.32/1.53          | ~ (v2_funct_1 @ X0)
% 1.32/1.53          | ~ (v1_funct_1 @ X0)
% 1.32/1.53          | ~ (v1_relat_1 @ X0)
% 1.32/1.53          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.32/1.53              = (k5_relat_1 @ 
% 1.32/1.53                 (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 1.32/1.53                 (k6_relat_1 @ (k2_relat_1 @ X0)))))),
% 1.32/1.53      inference('simplify', [status(thm)], ['51'])).
% 1.32/1.53  thf('53', plain,
% 1.32/1.53      (![X0 : $i]:
% 1.32/1.53         (~ (v1_relat_1 @ X0)
% 1.32/1.53          | ~ (v1_funct_1 @ X0)
% 1.32/1.53          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.32/1.53              = (k5_relat_1 @ 
% 1.32/1.53                 (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 1.32/1.53                 (k6_relat_1 @ (k2_relat_1 @ X0))))
% 1.32/1.53          | ~ (v1_relat_1 @ X0)
% 1.32/1.53          | ~ (v1_funct_1 @ X0)
% 1.32/1.53          | ~ (v2_funct_1 @ X0))),
% 1.32/1.53      inference('sup-', [status(thm)], ['48', '52'])).
% 1.32/1.53  thf('54', plain,
% 1.32/1.53      (![X0 : $i]:
% 1.32/1.53         (~ (v2_funct_1 @ X0)
% 1.32/1.53          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.32/1.53              = (k5_relat_1 @ 
% 1.32/1.53                 (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 1.32/1.53                 (k6_relat_1 @ (k2_relat_1 @ X0))))
% 1.32/1.53          | ~ (v1_funct_1 @ X0)
% 1.32/1.53          | ~ (v1_relat_1 @ X0))),
% 1.32/1.53      inference('simplify', [status(thm)], ['53'])).
% 1.32/1.53  thf('55', plain,
% 1.32/1.53      (![X0 : $i]:
% 1.32/1.53         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.32/1.53            = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 1.32/1.53               (k6_relat_1 @ (k2_relat_1 @ X0))))
% 1.32/1.53          | ~ (v1_relat_1 @ X0)
% 1.32/1.53          | ~ (v1_funct_1 @ X0)
% 1.32/1.53          | ~ (v2_funct_1 @ X0)
% 1.32/1.53          | ~ (v1_relat_1 @ X0)
% 1.32/1.53          | ~ (v1_funct_1 @ X0)
% 1.32/1.53          | ~ (v2_funct_1 @ X0))),
% 1.32/1.53      inference('sup+', [status(thm)], ['47', '54'])).
% 1.32/1.53  thf('56', plain,
% 1.32/1.53      (![X0 : $i]:
% 1.32/1.53         (~ (v2_funct_1 @ X0)
% 1.32/1.53          | ~ (v1_funct_1 @ X0)
% 1.32/1.53          | ~ (v1_relat_1 @ X0)
% 1.32/1.53          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.32/1.53              = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 1.32/1.53                 (k6_relat_1 @ (k2_relat_1 @ X0)))))),
% 1.32/1.53      inference('simplify', [status(thm)], ['55'])).
% 1.32/1.53  thf('57', plain,
% 1.32/1.53      ((((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)
% 1.32/1.53          = (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 1.32/1.53        | ~ (v1_relat_1 @ sk_B)
% 1.32/1.53        | ~ (v1_funct_1 @ sk_B)
% 1.32/1.53        | ~ (v2_funct_1 @ sk_B))),
% 1.32/1.53      inference('sup+', [status(thm)], ['46', '56'])).
% 1.32/1.53  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('59', plain, ((v1_funct_1 @ sk_B)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('60', plain,
% 1.32/1.53      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('61', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 1.32/1.53      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.32/1.53  thf('62', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_B @ sk_A))),
% 1.32/1.53      inference('sup+', [status(thm)], ['60', '61'])).
% 1.32/1.53  thf(t48_funct_1, axiom,
% 1.32/1.53    (![A:$i]:
% 1.32/1.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.32/1.53       ( ![B:$i]:
% 1.32/1.53         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.32/1.53           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.32/1.53               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 1.32/1.53             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 1.32/1.53  thf('63', plain,
% 1.32/1.53      (![X7 : $i, X8 : $i]:
% 1.32/1.53         (~ (v1_relat_1 @ X7)
% 1.32/1.53          | ~ (v1_funct_1 @ X7)
% 1.32/1.53          | (v2_funct_1 @ X7)
% 1.32/1.53          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 1.32/1.53          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 1.32/1.53          | ~ (v1_funct_1 @ X8)
% 1.32/1.53          | ~ (v1_relat_1 @ X8))),
% 1.32/1.53      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.32/1.53  thf('64', plain,
% 1.32/1.53      ((~ (v1_relat_1 @ sk_A)
% 1.32/1.53        | ~ (v1_funct_1 @ sk_A)
% 1.32/1.53        | ((k2_relat_1 @ sk_B) != (k1_relat_1 @ sk_A))
% 1.32/1.53        | (v2_funct_1 @ sk_B)
% 1.32/1.53        | ~ (v1_funct_1 @ sk_B)
% 1.32/1.53        | ~ (v1_relat_1 @ sk_B))),
% 1.32/1.53      inference('sup-', [status(thm)], ['62', '63'])).
% 1.32/1.53  thf('65', plain, ((v1_relat_1 @ sk_A)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('66', plain, ((v1_funct_1 @ sk_A)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('67', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('68', plain, ((v1_funct_1 @ sk_B)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('69', plain, ((v1_relat_1 @ sk_B)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('70', plain,
% 1.32/1.53      ((((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B)) | (v2_funct_1 @ sk_B))),
% 1.32/1.53      inference('demod', [status(thm)], ['64', '65', '66', '67', '68', '69'])).
% 1.32/1.53  thf('71', plain, ((v2_funct_1 @ sk_B)),
% 1.32/1.53      inference('simplify', [status(thm)], ['70'])).
% 1.32/1.53  thf('72', plain,
% 1.32/1.53      (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)
% 1.32/1.53         = (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 1.32/1.53      inference('demod', [status(thm)], ['57', '58', '59', '71'])).
% 1.32/1.53  thf('73', plain,
% 1.32/1.53      (![X4 : $i]:
% 1.32/1.53         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 1.32/1.53          | ~ (v1_funct_1 @ X4)
% 1.32/1.53          | ~ (v1_relat_1 @ X4))),
% 1.32/1.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.32/1.53  thf('74', plain,
% 1.32/1.53      (![X10 : $i]:
% 1.32/1.53         (~ (v2_funct_1 @ X10)
% 1.32/1.53          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 1.32/1.53              = (k6_relat_1 @ (k1_relat_1 @ X10)))
% 1.32/1.53          | ~ (v1_funct_1 @ X10)
% 1.32/1.53          | ~ (v1_relat_1 @ X10))),
% 1.32/1.53      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.32/1.53  thf('75', plain,
% 1.32/1.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.53         (~ (v1_relat_1 @ X0)
% 1.32/1.53          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 1.32/1.53              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 1.32/1.53          | ~ (v1_relat_1 @ X2)
% 1.32/1.53          | ~ (v1_relat_1 @ X1))),
% 1.32/1.53      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.32/1.53  thf('76', plain,
% 1.32/1.53      (![X0 : $i, X1 : $i]:
% 1.32/1.53         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1)
% 1.32/1.53            = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 1.32/1.53          | ~ (v1_relat_1 @ X0)
% 1.32/1.53          | ~ (v1_funct_1 @ X0)
% 1.32/1.53          | ~ (v2_funct_1 @ X0)
% 1.32/1.53          | ~ (v1_relat_1 @ X0)
% 1.32/1.53          | ~ (v1_relat_1 @ X1)
% 1.32/1.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.32/1.53      inference('sup+', [status(thm)], ['74', '75'])).
% 1.32/1.53  thf('77', plain,
% 1.32/1.53      (![X0 : $i, X1 : $i]:
% 1.32/1.53         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.32/1.53          | ~ (v1_relat_1 @ X1)
% 1.32/1.53          | ~ (v2_funct_1 @ X0)
% 1.32/1.53          | ~ (v1_funct_1 @ X0)
% 1.32/1.53          | ~ (v1_relat_1 @ X0)
% 1.32/1.53          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1)
% 1.32/1.53              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1))))),
% 1.32/1.53      inference('simplify', [status(thm)], ['76'])).
% 1.32/1.53  thf('78', plain,
% 1.32/1.53      (![X0 : $i, X1 : $i]:
% 1.32/1.53         (~ (v1_relat_1 @ X0)
% 1.32/1.53          | ~ (v1_funct_1 @ X0)
% 1.32/1.53          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1)
% 1.32/1.53              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 1.32/1.53          | ~ (v1_relat_1 @ X0)
% 1.32/1.53          | ~ (v1_funct_1 @ X0)
% 1.32/1.53          | ~ (v2_funct_1 @ X0)
% 1.32/1.53          | ~ (v1_relat_1 @ X1))),
% 1.32/1.53      inference('sup-', [status(thm)], ['73', '77'])).
% 1.32/1.53  thf('79', plain,
% 1.32/1.53      (![X0 : $i, X1 : $i]:
% 1.32/1.53         (~ (v1_relat_1 @ X1)
% 1.32/1.53          | ~ (v2_funct_1 @ X0)
% 1.32/1.53          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1)
% 1.32/1.53              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 1.32/1.53          | ~ (v1_funct_1 @ X0)
% 1.32/1.53          | ~ (v1_relat_1 @ X0))),
% 1.32/1.53      inference('simplify', [status(thm)], ['78'])).
% 1.32/1.53  thf('80', plain,
% 1.32/1.53      ((((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B)
% 1.32/1.53          = (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))
% 1.32/1.53        | ~ (v1_relat_1 @ sk_B)
% 1.32/1.53        | ~ (v1_funct_1 @ sk_B)
% 1.32/1.53        | ~ (v2_funct_1 @ sk_B)
% 1.32/1.53        | ~ (v1_relat_1 @ sk_B))),
% 1.32/1.53      inference('sup+', [status(thm)], ['72', '79'])).
% 1.32/1.53  thf('81', plain,
% 1.32/1.53      (![X10 : $i]:
% 1.32/1.53         (~ (v2_funct_1 @ X10)
% 1.32/1.53          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 1.32/1.53              = (k6_relat_1 @ (k1_relat_1 @ X10)))
% 1.32/1.53          | ~ (v1_funct_1 @ X10)
% 1.32/1.53          | ~ (v1_relat_1 @ X10))),
% 1.32/1.53      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.32/1.53  thf('82', plain,
% 1.32/1.53      (![X4 : $i]:
% 1.32/1.53         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 1.32/1.53          | ~ (v1_funct_1 @ X4)
% 1.32/1.53          | ~ (v1_relat_1 @ X4))),
% 1.32/1.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.32/1.53  thf('83', plain,
% 1.32/1.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.53         (~ (v1_relat_1 @ X0)
% 1.32/1.53          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 1.32/1.53              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 1.32/1.53          | ~ (v1_relat_1 @ X2)
% 1.32/1.53          | ~ (v1_relat_1 @ X1))),
% 1.32/1.53      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.32/1.53  thf('84', plain,
% 1.32/1.53      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('85', plain,
% 1.32/1.53      (![X4 : $i]:
% 1.32/1.53         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 1.32/1.53          | ~ (v1_funct_1 @ X4)
% 1.32/1.53          | ~ (v1_relat_1 @ X4))),
% 1.32/1.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.32/1.53  thf('86', plain,
% 1.32/1.53      (![X9 : $i]:
% 1.32/1.53         (~ (v2_funct_1 @ X9)
% 1.32/1.53          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 1.32/1.53          | ~ (v1_funct_1 @ X9)
% 1.32/1.53          | ~ (v1_relat_1 @ X9))),
% 1.32/1.53      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.32/1.53  thf('87', plain,
% 1.32/1.53      (![X3 : $i]:
% 1.32/1.53         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X3)) @ X3) = (X3))
% 1.32/1.53          | ~ (v1_relat_1 @ X3))),
% 1.32/1.53      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.32/1.53  thf('88', plain,
% 1.32/1.53      (![X0 : $i]:
% 1.32/1.53         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 1.32/1.53            = (k2_funct_1 @ X0))
% 1.32/1.53          | ~ (v1_relat_1 @ X0)
% 1.32/1.53          | ~ (v1_funct_1 @ X0)
% 1.32/1.53          | ~ (v2_funct_1 @ X0)
% 1.32/1.53          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.32/1.53      inference('sup+', [status(thm)], ['86', '87'])).
% 1.32/1.53  thf('89', plain,
% 1.32/1.53      (![X0 : $i]:
% 1.32/1.53         (~ (v1_relat_1 @ X0)
% 1.32/1.53          | ~ (v1_funct_1 @ X0)
% 1.32/1.53          | ~ (v2_funct_1 @ X0)
% 1.32/1.53          | ~ (v1_funct_1 @ X0)
% 1.32/1.53          | ~ (v1_relat_1 @ X0)
% 1.32/1.53          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 1.32/1.53              = (k2_funct_1 @ X0)))),
% 1.32/1.53      inference('sup-', [status(thm)], ['85', '88'])).
% 1.32/1.53  thf('90', plain,
% 1.32/1.53      (![X0 : $i]:
% 1.32/1.53         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 1.32/1.53            = (k2_funct_1 @ X0))
% 1.32/1.53          | ~ (v2_funct_1 @ X0)
% 1.32/1.53          | ~ (v1_funct_1 @ X0)
% 1.32/1.53          | ~ (v1_relat_1 @ X0))),
% 1.32/1.53      inference('simplify', [status(thm)], ['89'])).
% 1.32/1.53  thf('91', plain,
% 1.32/1.53      ((((k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ (k2_funct_1 @ sk_A))
% 1.32/1.53          = (k2_funct_1 @ sk_A))
% 1.32/1.53        | ~ (v1_relat_1 @ sk_A)
% 1.32/1.53        | ~ (v1_funct_1 @ sk_A)
% 1.32/1.53        | ~ (v2_funct_1 @ sk_A))),
% 1.32/1.53      inference('sup+', [status(thm)], ['84', '90'])).
% 1.32/1.53  thf('92', plain, ((v1_relat_1 @ sk_A)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('93', plain, ((v1_funct_1 @ sk_A)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('94', plain, ((v2_funct_1 @ sk_A)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('95', plain,
% 1.32/1.53      (((k5_relat_1 @ (k5_relat_1 @ sk_B @ sk_A) @ (k2_funct_1 @ sk_A))
% 1.32/1.53         = (k2_funct_1 @ sk_A))),
% 1.32/1.53      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 1.32/1.53  thf('96', plain,
% 1.32/1.53      ((((k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 1.32/1.53          = (k2_funct_1 @ sk_A))
% 1.32/1.53        | ~ (v1_relat_1 @ sk_B)
% 1.32/1.53        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 1.32/1.53        | ~ (v1_relat_1 @ sk_A))),
% 1.32/1.53      inference('sup+', [status(thm)], ['83', '95'])).
% 1.32/1.53  thf('97', plain, ((v1_relat_1 @ sk_B)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('98', plain, ((v1_relat_1 @ sk_A)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('99', plain,
% 1.32/1.53      ((((k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 1.32/1.53          = (k2_funct_1 @ sk_A))
% 1.32/1.53        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 1.32/1.53      inference('demod', [status(thm)], ['96', '97', '98'])).
% 1.32/1.53  thf('100', plain,
% 1.32/1.53      ((~ (v1_relat_1 @ sk_A)
% 1.32/1.53        | ~ (v1_funct_1 @ sk_A)
% 1.32/1.53        | ((k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 1.32/1.53            = (k2_funct_1 @ sk_A)))),
% 1.32/1.53      inference('sup-', [status(thm)], ['82', '99'])).
% 1.32/1.53  thf('101', plain, ((v1_relat_1 @ sk_A)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('102', plain, ((v1_funct_1 @ sk_A)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('103', plain,
% 1.32/1.53      (((k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ (k2_funct_1 @ sk_A)))
% 1.32/1.53         = (k2_funct_1 @ sk_A))),
% 1.32/1.53      inference('demod', [status(thm)], ['100', '101', '102'])).
% 1.32/1.53  thf('104', plain,
% 1.32/1.53      ((((k5_relat_1 @ sk_B @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 1.32/1.53          = (k2_funct_1 @ sk_A))
% 1.32/1.53        | ~ (v1_relat_1 @ sk_A)
% 1.32/1.53        | ~ (v1_funct_1 @ sk_A)
% 1.32/1.53        | ~ (v2_funct_1 @ sk_A))),
% 1.32/1.53      inference('sup+', [status(thm)], ['81', '103'])).
% 1.32/1.53  thf('105', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('106', plain, ((v1_relat_1 @ sk_A)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('107', plain, ((v1_funct_1 @ sk_A)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('108', plain, ((v2_funct_1 @ sk_A)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('109', plain,
% 1.32/1.53      (((k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 1.32/1.53         = (k2_funct_1 @ sk_A))),
% 1.32/1.53      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 1.32/1.53  thf('110', plain, ((v1_relat_1 @ sk_B)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('111', plain, ((v1_funct_1 @ sk_B)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('112', plain, ((v2_funct_1 @ sk_B)),
% 1.32/1.53      inference('simplify', [status(thm)], ['70'])).
% 1.32/1.53  thf('113', plain, ((v1_relat_1 @ sk_B)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('114', plain,
% 1.32/1.53      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B)
% 1.32/1.53         = (k2_funct_1 @ sk_A))),
% 1.32/1.53      inference('demod', [status(thm)],
% 1.32/1.53                ['80', '109', '110', '111', '112', '113'])).
% 1.32/1.53  thf('115', plain, ((((sk_B) = (k2_funct_1 @ sk_A)) | ~ (v1_relat_1 @ sk_B))),
% 1.32/1.53      inference('sup+', [status(thm)], ['0', '114'])).
% 1.32/1.53  thf('116', plain, ((v1_relat_1 @ sk_B)),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('117', plain, (((sk_B) = (k2_funct_1 @ sk_A))),
% 1.32/1.53      inference('demod', [status(thm)], ['115', '116'])).
% 1.32/1.53  thf('118', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 1.32/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.53  thf('119', plain, ($false),
% 1.32/1.53      inference('simplify_reflect-', [status(thm)], ['117', '118'])).
% 1.32/1.53  
% 1.32/1.53  % SZS output end Refutation
% 1.32/1.53  
% 1.39/1.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

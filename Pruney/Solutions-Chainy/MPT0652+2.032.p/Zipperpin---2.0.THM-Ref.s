%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kBxxqdDzLJ

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:32 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 116 expanded)
%              Number of leaves         :   21 (  40 expanded)
%              Depth                    :   19
%              Number of atoms          :  766 (1514 expanded)
%              Number of equality atoms :   67 ( 135 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t126_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A )
        = A ) ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X2 ) @ X2 )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('9',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t198_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( ( k1_relat_1 @ A )
                  = ( k1_relat_1 @ B ) )
               => ( ( k1_relat_1 @ ( k5_relat_1 @ C @ A ) )
                  = ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ X7 )
       != ( k1_relat_1 @ X6 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t198_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k8_relat_1 @ ( k1_relat_1 @ X1 ) @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t59_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v2_funct_1 @ A )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
              = ( k2_relat_1 @ A ) )
            & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t59_funct_1])).

thf('21',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X3: $i] :
      ( ( ( k9_relat_1 @ X3 @ ( k1_relat_1 @ X3 ) )
        = ( k2_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('25',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) )
        = ( k9_relat_1 @ X4 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('27',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('28',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k1_relat_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( ( k9_relat_1 @ sk_A @ ( k1_relat_1 @ sk_A ) )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,
    ( ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( ( k2_relat_1 @ sk_A )
       != ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
    = ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('45',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['43','44'])).

thf('46',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['22','45'])).

thf('47',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,(
    $false ),
    inference(simplify,[status(thm)],['56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kBxxqdDzLJ
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:25:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 57 iterations in 0.066s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.57  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.38/0.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.38/0.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.38/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.57  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.38/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.38/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.38/0.57  thf(t55_funct_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.57       ( ( v2_funct_1 @ A ) =>
% 0.38/0.57         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.38/0.57           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      (![X14 : $i]:
% 0.38/0.57         (~ (v2_funct_1 @ X14)
% 0.38/0.57          | ((k2_relat_1 @ X14) = (k1_relat_1 @ (k2_funct_1 @ X14)))
% 0.38/0.57          | ~ (v1_funct_1 @ X14)
% 0.38/0.57          | ~ (v1_relat_1 @ X14))),
% 0.38/0.57      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.57  thf(dt_k2_funct_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.57       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.38/0.57         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (![X11 : $i]:
% 0.38/0.57         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 0.38/0.57          | ~ (v1_funct_1 @ X11)
% 0.38/0.57          | ~ (v1_relat_1 @ X11))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (![X11 : $i]:
% 0.38/0.57         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 0.38/0.57          | ~ (v1_funct_1 @ X11)
% 0.38/0.57          | ~ (v1_relat_1 @ X11))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (![X14 : $i]:
% 0.38/0.57         (~ (v2_funct_1 @ X14)
% 0.38/0.57          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 0.38/0.57          | ~ (v1_funct_1 @ X14)
% 0.38/0.57          | ~ (v1_relat_1 @ X14))),
% 0.38/0.57      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.57  thf(t126_relat_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ A ) =>
% 0.38/0.57       ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A ) = ( A ) ) ))).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (![X2 : $i]:
% 0.38/0.57         (((k8_relat_1 @ (k2_relat_1 @ X2) @ X2) = (X2)) | ~ (v1_relat_1 @ X2))),
% 0.38/0.57      inference('cnf', [status(esa)], [t126_relat_1])).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((k8_relat_1 @ (k1_relat_1 @ X0) @ (k2_funct_1 @ X0))
% 0.38/0.57            = (k2_funct_1 @ X0))
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['3', '4'])).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ((k8_relat_1 @ (k1_relat_1 @ X0) @ (k2_funct_1 @ X0))
% 0.38/0.57              = (k2_funct_1 @ X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['2', '5'])).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((k8_relat_1 @ (k1_relat_1 @ X0) @ (k2_funct_1 @ X0))
% 0.38/0.57            = (k2_funct_1 @ X0))
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0))),
% 0.38/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.38/0.57  thf(t123_relat_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ B ) =>
% 0.38/0.57       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((k8_relat_1 @ X1 @ X0) = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.38/0.57          | ~ (v1_relat_1 @ X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.38/0.57  thf(t71_relat_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.38/0.57       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.38/0.57  thf('9', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.38/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.57  thf(t198_relat_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( v1_relat_1 @ B ) =>
% 0.38/0.57           ( ![C:$i]:
% 0.38/0.57             ( ( v1_relat_1 @ C ) =>
% 0.38/0.57               ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) =>
% 0.38/0.57                 ( ( k1_relat_1 @ ( k5_relat_1 @ C @ A ) ) =
% 0.38/0.57                   ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X6)
% 0.38/0.57          | ((k1_relat_1 @ X7) != (k1_relat_1 @ X6))
% 0.38/0.57          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 0.38/0.57              = (k1_relat_1 @ (k5_relat_1 @ X8 @ X6)))
% 0.38/0.57          | ~ (v1_relat_1 @ X8)
% 0.38/0.57          | ~ (v1_relat_1 @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [t198_relat_1])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.57         (((X0) != (k1_relat_1 @ X1))
% 0.38/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.38/0.57          | ~ (v1_relat_1 @ X2)
% 0.38/0.57          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.38/0.57              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.38/0.57          | ~ (v1_relat_1 @ X1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.57  thf(fc3_funct_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.38/0.57       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.38/0.57  thf('12', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.57         (((X0) != (k1_relat_1 @ X1))
% 0.38/0.57          | ~ (v1_relat_1 @ X2)
% 0.38/0.57          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.38/0.57              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.38/0.57          | ~ (v1_relat_1 @ X1))),
% 0.38/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (![X1 : $i, X2 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X1)
% 0.38/0.57          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ (k1_relat_1 @ X1))))
% 0.38/0.57              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.38/0.57          | ~ (v1_relat_1 @ X2))),
% 0.38/0.57      inference('simplify', [status(thm)], ['13'])).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((k1_relat_1 @ (k8_relat_1 @ (k1_relat_1 @ X1) @ X0))
% 0.38/0.57            = (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X1))),
% 0.38/0.57      inference('sup+', [status(thm)], ['8', '14'])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X1)
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ((k1_relat_1 @ (k8_relat_1 @ (k1_relat_1 @ X1) @ X0))
% 0.38/0.57              = (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 0.38/0.57      inference('simplify', [status(thm)], ['15'])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((k1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.57            = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.57          | ~ (v1_relat_1 @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['7', '16'])).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.57          | ~ (v2_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.57              = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))))),
% 0.38/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.57              = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v2_funct_1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['1', '18'])).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v2_funct_1 @ X0)
% 0.38/0.57          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.57              = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0))),
% 0.38/0.57      inference('simplify', [status(thm)], ['19'])).
% 0.38/0.57  thf(t59_funct_1, conjecture,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.57       ( ( v2_funct_1 @ A ) =>
% 0.38/0.57         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.38/0.57             ( k2_relat_1 @ A ) ) & 
% 0.38/0.57           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.38/0.57             ( k2_relat_1 @ A ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i]:
% 0.38/0.57        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.57          ( ( v2_funct_1 @ A ) =>
% 0.38/0.57            ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.38/0.57                ( k2_relat_1 @ A ) ) & 
% 0.38/0.57              ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.38/0.57                ( k2_relat_1 @ A ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t59_funct_1])).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.57          != (k2_relat_1 @ sk_A))
% 0.38/0.57        | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.57            != (k2_relat_1 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      ((((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.57          != (k2_relat_1 @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.57                = (k2_relat_1 @ sk_A))))),
% 0.38/0.57      inference('split', [status(esa)], ['21'])).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      (![X11 : $i]:
% 0.38/0.57         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 0.38/0.57          | ~ (v1_funct_1 @ X11)
% 0.38/0.57          | ~ (v1_relat_1 @ X11))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.57  thf(t146_relat_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ A ) =>
% 0.38/0.57       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      (![X3 : $i]:
% 0.38/0.57         (((k9_relat_1 @ X3 @ (k1_relat_1 @ X3)) = (k2_relat_1 @ X3))
% 0.38/0.57          | ~ (v1_relat_1 @ X3))),
% 0.38/0.57      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (![X14 : $i]:
% 0.38/0.57         (~ (v2_funct_1 @ X14)
% 0.38/0.57          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 0.38/0.57          | ~ (v1_funct_1 @ X14)
% 0.38/0.57          | ~ (v1_relat_1 @ X14))),
% 0.38/0.57      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.57  thf(t160_relat_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( v1_relat_1 @ B ) =>
% 0.38/0.57           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.38/0.57             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      (![X4 : $i, X5 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X4)
% 0.38/0.57          | ((k2_relat_1 @ (k5_relat_1 @ X5 @ X4))
% 0.38/0.57              = (k9_relat_1 @ X4 @ (k2_relat_1 @ X5)))
% 0.38/0.57          | ~ (v1_relat_1 @ X5))),
% 0.38/0.57      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      ((((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.57          != (k2_relat_1 @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.57                = (k2_relat_1 @ sk_A))))),
% 0.38/0.57      inference('split', [status(esa)], ['21'])).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      (((((k9_relat_1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.38/0.57           != (k2_relat_1 @ sk_A))
% 0.38/0.57         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.38/0.57         | ~ (v1_relat_1 @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.57                = (k2_relat_1 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.57  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('30', plain,
% 0.38/0.57      (((((k9_relat_1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.38/0.57           != (k2_relat_1 @ sk_A))
% 0.38/0.57         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.57                = (k2_relat_1 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['28', '29'])).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      (((((k9_relat_1 @ sk_A @ (k1_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.38/0.57         | ~ (v1_relat_1 @ sk_A)
% 0.38/0.57         | ~ (v1_funct_1 @ sk_A)
% 0.38/0.57         | ~ (v2_funct_1 @ sk_A)
% 0.38/0.57         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.57                = (k2_relat_1 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['25', '30'])).
% 0.38/0.57  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('33', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('34', plain, ((v2_funct_1 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      (((((k9_relat_1 @ sk_A @ (k1_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.38/0.57         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.57                = (k2_relat_1 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.38/0.57  thf('36', plain,
% 0.38/0.57      (((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.38/0.57         | ~ (v1_relat_1 @ sk_A)
% 0.38/0.57         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.57                = (k2_relat_1 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['24', '35'])).
% 0.38/0.57  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      (((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.38/0.57         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.57                = (k2_relat_1 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['36', '37'])).
% 0.38/0.57  thf('39', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.57                = (k2_relat_1 @ sk_A))))),
% 0.38/0.57      inference('simplify', [status(thm)], ['38'])).
% 0.38/0.57  thf('40', plain,
% 0.38/0.57      (((~ (v1_relat_1 @ sk_A) | ~ (v1_funct_1 @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.57                = (k2_relat_1 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['23', '39'])).
% 0.38/0.57  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('42', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('43', plain,
% 0.38/0.57      ((((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.57          = (k2_relat_1 @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.38/0.57  thf('44', plain,
% 0.38/0.57      (~
% 0.38/0.57       (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.57          = (k2_relat_1 @ sk_A))) | 
% 0.38/0.57       ~
% 0.38/0.57       (((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.57          = (k2_relat_1 @ sk_A)))),
% 0.38/0.57      inference('split', [status(esa)], ['21'])).
% 0.38/0.57  thf('45', plain,
% 0.38/0.57      (~
% 0.38/0.57       (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.57          = (k2_relat_1 @ sk_A)))),
% 0.38/0.57      inference('sat_resolution*', [status(thm)], ['43', '44'])).
% 0.38/0.57  thf('46', plain,
% 0.38/0.57      (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 0.38/0.57         != (k2_relat_1 @ sk_A))),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['22', '45'])).
% 0.38/0.57  thf('47', plain,
% 0.38/0.57      ((((k1_relat_1 @ (k2_funct_1 @ sk_A)) != (k2_relat_1 @ sk_A))
% 0.38/0.57        | ~ (v1_relat_1 @ sk_A)
% 0.38/0.57        | ~ (v1_funct_1 @ sk_A)
% 0.38/0.57        | ~ (v2_funct_1 @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['20', '46'])).
% 0.38/0.57  thf('48', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('49', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('50', plain, ((v2_funct_1 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('51', plain,
% 0.38/0.57      (((k1_relat_1 @ (k2_funct_1 @ sk_A)) != (k2_relat_1 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.38/0.57  thf('52', plain,
% 0.38/0.57      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))
% 0.38/0.57        | ~ (v1_relat_1 @ sk_A)
% 0.38/0.57        | ~ (v1_funct_1 @ sk_A)
% 0.38/0.57        | ~ (v2_funct_1 @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['0', '51'])).
% 0.38/0.57  thf('53', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('54', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('55', plain, ((v2_funct_1 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('56', plain, (((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.38/0.57  thf('57', plain, ($false), inference('simplify', [status(thm)], ['56'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

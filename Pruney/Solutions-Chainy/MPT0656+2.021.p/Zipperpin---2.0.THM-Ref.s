%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vf9omIif7i

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:39 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 112 expanded)
%              Number of leaves         :   20 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  656 (1676 expanded)
%              Number of equality atoms :   48 ( 164 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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

thf('2',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ X5 @ ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('12',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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

thf('13',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X11 ) @ X11 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ sk_B )
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','18'])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) ) )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
      = ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['21','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

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

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ ( k1_relat_1 @ X8 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('32',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33','34','35','36','37'])).

thf('39',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X4 ) @ X3 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
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

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( sk_B
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','43','44','45','46','47'])).

thf('49',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vf9omIif7i
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 142 iterations in 0.129s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.61  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.37/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.61  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.37/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.37/0.61  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.37/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.61  thf(t63_funct_1, conjecture,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.61           ( ( ( v2_funct_1 @ A ) & 
% 0.37/0.61               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.37/0.61               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.37/0.61             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i]:
% 0.37/0.61        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.61          ( ![B:$i]:
% 0.37/0.61            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.61              ( ( ( v2_funct_1 @ A ) & 
% 0.37/0.61                  ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.37/0.61                  ( ( k5_relat_1 @ A @ B ) =
% 0.37/0.61                    ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.37/0.61                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t63_funct_1])).
% 0.37/0.61  thf('0', plain,
% 0.37/0.61      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(dt_k2_funct_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.61       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.37/0.61         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.37/0.61  thf('1', plain,
% 0.37/0.61      (![X6 : $i]:
% 0.37/0.61         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 0.37/0.61          | ~ (v1_funct_1 @ X6)
% 0.37/0.61          | ~ (v1_relat_1 @ X6))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.37/0.61  thf(t55_funct_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.61       ( ( v2_funct_1 @ A ) =>
% 0.37/0.61         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.37/0.61           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.37/0.61  thf('2', plain,
% 0.37/0.61      (![X9 : $i]:
% 0.37/0.61         (~ (v2_funct_1 @ X9)
% 0.37/0.61          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.37/0.61          | ~ (v1_funct_1 @ X9)
% 0.37/0.61          | ~ (v1_relat_1 @ X9))),
% 0.37/0.61      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.37/0.61  thf(t80_relat_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ A ) =>
% 0.37/0.61       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.37/0.61  thf('3', plain,
% 0.37/0.61      (![X5 : $i]:
% 0.37/0.61         (((k5_relat_1 @ X5 @ (k6_relat_1 @ (k2_relat_1 @ X5))) = (X5))
% 0.37/0.61          | ~ (v1_relat_1 @ X5))),
% 0.37/0.61      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.37/0.61  thf('4', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.37/0.61            = (k2_funct_1 @ X0))
% 0.37/0.61          | ~ (v1_relat_1 @ X0)
% 0.37/0.61          | ~ (v1_funct_1 @ X0)
% 0.37/0.61          | ~ (v2_funct_1 @ X0)
% 0.37/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.37/0.61      inference('sup+', [status(thm)], ['2', '3'])).
% 0.37/0.61  thf('5', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X0)
% 0.37/0.61          | ~ (v1_funct_1 @ X0)
% 0.37/0.61          | ~ (v2_funct_1 @ X0)
% 0.37/0.61          | ~ (v1_funct_1 @ X0)
% 0.37/0.61          | ~ (v1_relat_1 @ X0)
% 0.37/0.61          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.37/0.61              = (k2_funct_1 @ X0)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['1', '4'])).
% 0.37/0.61  thf('6', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.37/0.61            = (k2_funct_1 @ X0))
% 0.37/0.61          | ~ (v2_funct_1 @ X0)
% 0.37/0.61          | ~ (v1_funct_1 @ X0)
% 0.37/0.61          | ~ (v1_relat_1 @ X0))),
% 0.37/0.61      inference('simplify', [status(thm)], ['5'])).
% 0.37/0.61  thf('7', plain,
% 0.37/0.61      ((((k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B))
% 0.37/0.61          = (k2_funct_1 @ sk_A))
% 0.37/0.61        | ~ (v1_relat_1 @ sk_A)
% 0.37/0.61        | ~ (v1_funct_1 @ sk_A)
% 0.37/0.61        | ~ (v2_funct_1 @ sk_A))),
% 0.37/0.61      inference('sup+', [status(thm)], ['0', '6'])).
% 0.37/0.61  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('9', plain, ((v1_funct_1 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('10', plain, ((v2_funct_1 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('11', plain,
% 0.37/0.61      (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B))
% 0.37/0.61         = (k2_funct_1 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.37/0.61  thf('12', plain,
% 0.37/0.61      (![X6 : $i]:
% 0.37/0.61         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 0.37/0.61          | ~ (v1_funct_1 @ X6)
% 0.37/0.61          | ~ (v1_relat_1 @ X6))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.37/0.61  thf(t61_funct_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.61       ( ( v2_funct_1 @ A ) =>
% 0.37/0.61         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.37/0.61             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.37/0.61           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.37/0.61             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.37/0.61  thf('13', plain,
% 0.37/0.61      (![X11 : $i]:
% 0.37/0.61         (~ (v2_funct_1 @ X11)
% 0.37/0.61          | ((k5_relat_1 @ (k2_funct_1 @ X11) @ X11)
% 0.37/0.61              = (k6_relat_1 @ (k2_relat_1 @ X11)))
% 0.37/0.61          | ~ (v1_funct_1 @ X11)
% 0.37/0.61          | ~ (v1_relat_1 @ X11))),
% 0.37/0.61      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.37/0.61  thf(t55_relat_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ A ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( v1_relat_1 @ B ) =>
% 0.37/0.61           ( ![C:$i]:
% 0.37/0.61             ( ( v1_relat_1 @ C ) =>
% 0.37/0.61               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.37/0.61                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X0)
% 0.37/0.61          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.37/0.61              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 0.37/0.61          | ~ (v1_relat_1 @ X2)
% 0.37/0.61          | ~ (v1_relat_1 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.37/0.61  thf('15', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)
% 0.37/0.61            = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.37/0.61          | ~ (v1_relat_1 @ X0)
% 0.37/0.61          | ~ (v1_funct_1 @ X0)
% 0.37/0.61          | ~ (v2_funct_1 @ X0)
% 0.37/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.37/0.61          | ~ (v1_relat_1 @ X1)
% 0.37/0.61          | ~ (v1_relat_1 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['13', '14'])).
% 0.37/0.61  thf('16', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X1)
% 0.37/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.37/0.61          | ~ (v2_funct_1 @ X0)
% 0.37/0.61          | ~ (v1_funct_1 @ X0)
% 0.37/0.61          | ~ (v1_relat_1 @ X0)
% 0.37/0.61          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)
% 0.37/0.61              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1))))),
% 0.37/0.61      inference('simplify', [status(thm)], ['15'])).
% 0.37/0.61  thf('17', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X0)
% 0.37/0.61          | ~ (v1_funct_1 @ X0)
% 0.37/0.61          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)
% 0.37/0.61              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.37/0.61          | ~ (v1_relat_1 @ X0)
% 0.37/0.61          | ~ (v1_funct_1 @ X0)
% 0.37/0.61          | ~ (v2_funct_1 @ X0)
% 0.37/0.61          | ~ (v1_relat_1 @ X1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['12', '16'])).
% 0.37/0.61  thf('18', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X1)
% 0.37/0.61          | ~ (v2_funct_1 @ X0)
% 0.37/0.61          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)
% 0.37/0.61              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.37/0.61          | ~ (v1_funct_1 @ X0)
% 0.37/0.61          | ~ (v1_relat_1 @ X0))),
% 0.37/0.61      inference('simplify', [status(thm)], ['17'])).
% 0.37/0.61  thf('19', plain,
% 0.37/0.61      ((((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ sk_B)
% 0.37/0.61          = (k2_funct_1 @ sk_A))
% 0.37/0.61        | ~ (v1_relat_1 @ sk_A)
% 0.37/0.61        | ~ (v1_funct_1 @ sk_A)
% 0.37/0.61        | ~ (v2_funct_1 @ sk_A)
% 0.37/0.61        | ~ (v1_relat_1 @ sk_B))),
% 0.37/0.61      inference('sup+', [status(thm)], ['11', '18'])).
% 0.37/0.61  thf('20', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('21', plain,
% 0.37/0.61      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('22', plain,
% 0.37/0.61      (![X11 : $i]:
% 0.37/0.61         (~ (v2_funct_1 @ X11)
% 0.37/0.61          | ((k5_relat_1 @ X11 @ (k2_funct_1 @ X11))
% 0.37/0.61              = (k6_relat_1 @ (k1_relat_1 @ X11)))
% 0.37/0.61          | ~ (v1_funct_1 @ X11)
% 0.37/0.61          | ~ (v1_relat_1 @ X11))),
% 0.37/0.61      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.37/0.61  thf(t58_funct_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.61       ( ( v2_funct_1 @ A ) =>
% 0.37/0.61         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.37/0.61             ( k1_relat_1 @ A ) ) & 
% 0.37/0.61           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.37/0.61             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.37/0.61  thf('23', plain,
% 0.37/0.61      (![X10 : $i]:
% 0.37/0.61         (~ (v2_funct_1 @ X10)
% 0.37/0.61          | ((k1_relat_1 @ (k5_relat_1 @ X10 @ (k2_funct_1 @ X10)))
% 0.37/0.61              = (k1_relat_1 @ X10))
% 0.37/0.61          | ~ (v1_funct_1 @ X10)
% 0.37/0.61          | ~ (v1_relat_1 @ X10))),
% 0.37/0.61      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.37/0.61  thf('24', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (((k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0))
% 0.37/0.61          | ~ (v1_relat_1 @ X0)
% 0.37/0.61          | ~ (v1_funct_1 @ X0)
% 0.37/0.61          | ~ (v2_funct_1 @ X0)
% 0.37/0.61          | ~ (v1_relat_1 @ X0)
% 0.37/0.61          | ~ (v1_funct_1 @ X0)
% 0.37/0.61          | ~ (v2_funct_1 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['22', '23'])).
% 0.37/0.61  thf('25', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (v2_funct_1 @ X0)
% 0.37/0.61          | ~ (v1_funct_1 @ X0)
% 0.37/0.61          | ~ (v1_relat_1 @ X0)
% 0.37/0.61          | ((k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.37/0.61              = (k1_relat_1 @ X0)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['24'])).
% 0.37/0.61  thf('26', plain,
% 0.37/0.61      ((((k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) = (k1_relat_1 @ sk_A))
% 0.37/0.61        | ~ (v1_relat_1 @ sk_A)
% 0.37/0.61        | ~ (v1_funct_1 @ sk_A)
% 0.37/0.61        | ~ (v2_funct_1 @ sk_A))),
% 0.37/0.61      inference('sup+', [status(thm)], ['21', '25'])).
% 0.37/0.61  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('28', plain, ((v1_funct_1 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('29', plain, ((v2_funct_1 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('30', plain,
% 0.37/0.61      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) = (k1_relat_1 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.37/0.61  thf(t27_funct_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.61           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 0.37/0.61             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.37/0.61  thf('31', plain,
% 0.37/0.61      (![X7 : $i, X8 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X7)
% 0.37/0.61          | ~ (v1_funct_1 @ X7)
% 0.37/0.61          | (r1_tarski @ (k2_relat_1 @ X7) @ (k1_relat_1 @ X8))
% 0.37/0.61          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X8)) != (k1_relat_1 @ X7))
% 0.37/0.61          | ~ (v1_funct_1 @ X8)
% 0.37/0.61          | ~ (v1_relat_1 @ X8))),
% 0.37/0.61      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.37/0.61  thf('32', plain,
% 0.37/0.61      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.37/0.61        | ~ (v1_relat_1 @ sk_B)
% 0.37/0.61        | ~ (v1_funct_1 @ sk_B)
% 0.37/0.61        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.37/0.61        | ~ (v1_funct_1 @ sk_A)
% 0.37/0.61        | ~ (v1_relat_1 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.61  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('34', plain, ((v1_funct_1 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('35', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('36', plain, ((v1_funct_1 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('38', plain,
% 0.37/0.61      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 0.37/0.61        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 0.37/0.61      inference('demod', [status(thm)], ['32', '33', '34', '35', '36', '37'])).
% 0.37/0.61  thf('39', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.37/0.61      inference('simplify', [status(thm)], ['38'])).
% 0.37/0.61  thf(t77_relat_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ B ) =>
% 0.37/0.61       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.37/0.61         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.37/0.61  thf('40', plain,
% 0.37/0.61      (![X3 : $i, X4 : $i]:
% 0.37/0.61         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 0.37/0.61          | ((k5_relat_1 @ (k6_relat_1 @ X4) @ X3) = (X3))
% 0.37/0.61          | ~ (v1_relat_1 @ X3))),
% 0.37/0.61      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.37/0.61  thf('41', plain,
% 0.37/0.61      ((~ (v1_relat_1 @ sk_B)
% 0.37/0.61        | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B) = (sk_B)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.61  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('43', plain,
% 0.37/0.61      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B) = (sk_B))),
% 0.37/0.61      inference('demod', [status(thm)], ['41', '42'])).
% 0.37/0.61  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('45', plain, ((v1_funct_1 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('46', plain, ((v2_funct_1 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('48', plain, (((sk_B) = (k2_funct_1 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)],
% 0.37/0.61                ['19', '20', '43', '44', '45', '46', '47'])).
% 0.37/0.61  thf('49', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('50', plain, ($false),
% 0.37/0.61      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

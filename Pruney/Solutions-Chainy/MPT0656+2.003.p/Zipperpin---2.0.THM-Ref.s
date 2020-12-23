%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HUhFooZpkC

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:36 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  229 (16116 expanded)
%              Number of leaves         :   23 (4883 expanded)
%              Depth                    :   38
%              Number of atoms          : 1679 (243271 expanded)
%              Number of equality atoms :  117 (24876 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ X7 @ ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

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

thf('1',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_funct_1 @ X8 )
        = ( k4_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k2_funct_1 @ sk_B )
      = ( k4_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k2_funct_1 @ sk_B )
      = ( k4_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('8',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('9',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('10',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ X7 @ ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('12',plain,
    ( ( ( k5_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k5_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
      = ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k5_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
      = ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k5_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf(t53_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ? [B: $i] :
            ( ( ( k5_relat_1 @ A @ B )
              = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
            & ( v1_funct_1 @ B )
            & ( v1_relat_1 @ B ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( ( k5_relat_1 @ X15 @ X14 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X15 ) ) )
      | ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t53_funct_1])).

thf('22',plain,
    ( ( ( k5_relat_1 @ sk_A @ sk_B )
     != ( k6_relat_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('25',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_funct_1 @ X8 )
        = ( k4_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('30',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_funct_1 @ sk_A )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('34',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('35',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('36',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_funct_1 @ X8 )
        = ( k4_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_A ) )
      = ( k4_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('44',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('45',plain,
    ( ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ( ( k2_funct_1 @ ( k4_relat_1 @ sk_A ) )
      = ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','44'])).

thf('46',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('47',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('48',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X16 ) @ X16 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('49',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

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

thf('55',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('56',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k1_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('60',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('61',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('66',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('67',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k1_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','58','64','70'])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ X7 @ ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('74',plain,
    ( ( ( k5_relat_1 @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k5_relat_1 @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X12 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('78',plain,
    ( ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) )
    | ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('81',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('82',plain,
    ( ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('86',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('87',plain,(
    v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','86'])).

thf('88',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('89',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('90',plain,
    ( ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('94',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('95',plain,(
    v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['90','91','92','93','94'])).

thf('96',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('98',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['78','79','87','95','96','97','98','99'])).

thf('101',plain,(
    v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) )
     != ( k1_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','101'])).

thf('103',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_A ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','106'])).

thf('108',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X16 ) @ X16 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('109',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) @ ( k4_relat_1 @ sk_A ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('111',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('112',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['105'])).

thf('113',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) @ ( k4_relat_1 @ sk_A ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['109','110','111','112'])).

thf('114',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('115',plain,
    ( ( v1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('117',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('118',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_A ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','106'])).

thf('119',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('120',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('122',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('123',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_A ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','106'])).

thf('125',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('126',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('128',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('129',plain,(
    v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,(
    v1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['115','116','117','123','129'])).

thf('131',plain,
    ( ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['27','130'])).

thf('132',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,(
    v1_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('136',plain,
    ( ( ( k5_relat_1 @ sk_A @ sk_B )
     != ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','25','26','134','135'])).

thf('137',plain,
    ( ( v2_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','137'])).

thf('139',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['138','139','140','141','142'])).

thf('144',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X12 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('145',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ sk_B ) )
    | ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ( v2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['145','146','147','148','149','150'])).

thf('152',plain,(
    v2_funct_1 @ sk_B ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['5','152'])).

thf('154',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X16 ) @ X16 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('155',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v2_funct_1 @ sk_B ),
    inference(simplify,[status(thm)],['151'])).

thf('159',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['155','156','157','158'])).

thf('160',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['5','152'])).

thf('161',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k5_relat_1 @ X16 @ ( k2_funct_1 @ X16 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('162',plain,
    ( ( ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v2_funct_1 @ sk_B ),
    inference(simplify,[status(thm)],['151'])).

thf('166',plain,
    ( ( k5_relat_1 @ sk_B @ ( k4_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['162','163','164','165'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('167',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['5','152'])).

thf('171',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('172',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['170','171'])).

thf('173',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['172','173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['168','169','175'])).

thf('177',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
      = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['159','176'])).

thf('178',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('180',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ X7 @ ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['179','180'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('182',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['181','182'])).

thf('184',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['178','183'])).

thf('185',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ sk_A )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('188',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['187','188'])).

thf('190',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('191',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['189','190','191'])).

thf('193',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['186','192'])).

thf('194',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( k4_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['177','195','196'])).

thf('198',plain,
    ( ( ( k4_relat_1 @ sk_A )
      = sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','197'])).

thf('199',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( k4_relat_1 @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('203',plain,(
    sk_B
 != ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['200','203'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HUhFooZpkC
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.20/1.39  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.20/1.39  % Solved by: fo/fo7.sh
% 1.20/1.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.20/1.39  % done 1188 iterations in 0.933s
% 1.20/1.39  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.20/1.39  % SZS output start Refutation
% 1.20/1.39  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.20/1.39  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.20/1.39  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.20/1.39  thf(sk_A_type, type, sk_A: $i).
% 1.20/1.39  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.20/1.39  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.20/1.39  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.20/1.39  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.20/1.39  thf(sk_B_type, type, sk_B: $i).
% 1.20/1.39  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.20/1.39  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.20/1.39  thf(t80_relat_1, axiom,
% 1.20/1.39    (![A:$i]:
% 1.20/1.39     ( ( v1_relat_1 @ A ) =>
% 1.20/1.39       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.20/1.39  thf('0', plain,
% 1.20/1.39      (![X7 : $i]:
% 1.20/1.39         (((k5_relat_1 @ X7 @ (k6_relat_1 @ (k2_relat_1 @ X7))) = (X7))
% 1.20/1.39          | ~ (v1_relat_1 @ X7))),
% 1.20/1.39      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.20/1.39  thf(t63_funct_1, conjecture,
% 1.20/1.39    (![A:$i]:
% 1.20/1.39     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.39       ( ![B:$i]:
% 1.20/1.39         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.20/1.39           ( ( ( v2_funct_1 @ A ) & 
% 1.20/1.39               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.20/1.39               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 1.20/1.39             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.20/1.39  thf(zf_stmt_0, negated_conjecture,
% 1.20/1.39    (~( ![A:$i]:
% 1.20/1.39        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.39          ( ![B:$i]:
% 1.20/1.39            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.20/1.39              ( ( ( v2_funct_1 @ A ) & 
% 1.20/1.39                  ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.20/1.39                  ( ( k5_relat_1 @ A @ B ) =
% 1.20/1.39                    ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 1.20/1.39                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 1.20/1.39    inference('cnf.neg', [status(esa)], [t63_funct_1])).
% 1.20/1.39  thf('1', plain, ((v1_relat_1 @ sk_B)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf(d9_funct_1, axiom,
% 1.20/1.39    (![A:$i]:
% 1.20/1.39     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.39       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.20/1.39  thf('2', plain,
% 1.20/1.39      (![X8 : $i]:
% 1.20/1.39         (~ (v2_funct_1 @ X8)
% 1.20/1.39          | ((k2_funct_1 @ X8) = (k4_relat_1 @ X8))
% 1.20/1.39          | ~ (v1_funct_1 @ X8)
% 1.20/1.39          | ~ (v1_relat_1 @ X8))),
% 1.20/1.39      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.20/1.39  thf('3', plain,
% 1.20/1.39      ((~ (v1_funct_1 @ sk_B)
% 1.20/1.39        | ((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))
% 1.20/1.39        | ~ (v2_funct_1 @ sk_B))),
% 1.20/1.39      inference('sup-', [status(thm)], ['1', '2'])).
% 1.20/1.39  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('5', plain,
% 1.20/1.39      ((((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B)) | ~ (v2_funct_1 @ sk_B))),
% 1.20/1.39      inference('demod', [status(thm)], ['3', '4'])).
% 1.20/1.39  thf(fc2_funct_1, axiom,
% 1.20/1.39    (![A:$i,B:$i]:
% 1.20/1.39     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 1.20/1.39         ( v1_funct_1 @ B ) ) =>
% 1.20/1.39       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 1.20/1.39         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 1.20/1.39  thf('6', plain,
% 1.20/1.39      (![X10 : $i, X11 : $i]:
% 1.20/1.39         (~ (v1_funct_1 @ X10)
% 1.20/1.39          | ~ (v1_relat_1 @ X10)
% 1.20/1.39          | ~ (v1_relat_1 @ X11)
% 1.20/1.39          | ~ (v1_funct_1 @ X11)
% 1.20/1.39          | (v1_relat_1 @ (k5_relat_1 @ X10 @ X11)))),
% 1.20/1.39      inference('cnf', [status(esa)], [fc2_funct_1])).
% 1.20/1.39  thf('7', plain,
% 1.20/1.39      (![X10 : $i, X11 : $i]:
% 1.20/1.39         (~ (v1_funct_1 @ X10)
% 1.20/1.39          | ~ (v1_relat_1 @ X10)
% 1.20/1.39          | ~ (v1_relat_1 @ X11)
% 1.20/1.39          | ~ (v1_funct_1 @ X11)
% 1.20/1.39          | (v1_relat_1 @ (k5_relat_1 @ X10 @ X11)))),
% 1.20/1.39      inference('cnf', [status(esa)], [fc2_funct_1])).
% 1.20/1.39  thf('8', plain,
% 1.20/1.39      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf(t71_relat_1, axiom,
% 1.20/1.39    (![A:$i]:
% 1.20/1.39     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.20/1.39       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.20/1.39  thf('9', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 1.20/1.39      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.20/1.39  thf('10', plain,
% 1.20/1.39      (((k2_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) = (k1_relat_1 @ sk_A))),
% 1.20/1.39      inference('sup+', [status(thm)], ['8', '9'])).
% 1.20/1.39  thf('11', plain,
% 1.20/1.39      (![X7 : $i]:
% 1.20/1.39         (((k5_relat_1 @ X7 @ (k6_relat_1 @ (k2_relat_1 @ X7))) = (X7))
% 1.20/1.39          | ~ (v1_relat_1 @ X7))),
% 1.20/1.39      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.20/1.39  thf('12', plain,
% 1.20/1.39      ((((k5_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 1.20/1.39          (k6_relat_1 @ (k1_relat_1 @ sk_A))) = (k5_relat_1 @ sk_A @ sk_B))
% 1.20/1.39        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 1.20/1.39      inference('sup+', [status(thm)], ['10', '11'])).
% 1.20/1.39  thf('13', plain,
% 1.20/1.39      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('14', plain,
% 1.20/1.39      ((((k5_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ (k5_relat_1 @ sk_A @ sk_B))
% 1.20/1.39          = (k5_relat_1 @ sk_A @ sk_B))
% 1.20/1.39        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 1.20/1.39      inference('demod', [status(thm)], ['12', '13'])).
% 1.20/1.39  thf('15', plain,
% 1.20/1.39      ((~ (v1_funct_1 @ sk_B)
% 1.20/1.39        | ~ (v1_relat_1 @ sk_B)
% 1.20/1.39        | ~ (v1_relat_1 @ sk_A)
% 1.20/1.39        | ~ (v1_funct_1 @ sk_A)
% 1.20/1.39        | ((k5_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 1.20/1.39            (k5_relat_1 @ sk_A @ sk_B)) = (k5_relat_1 @ sk_A @ sk_B)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['7', '14'])).
% 1.20/1.39  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('19', plain, ((v1_funct_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('20', plain,
% 1.20/1.39      (((k5_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ (k5_relat_1 @ sk_A @ sk_B))
% 1.20/1.39         = (k5_relat_1 @ sk_A @ sk_B))),
% 1.20/1.39      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 1.20/1.39  thf(t53_funct_1, axiom,
% 1.20/1.39    (![A:$i]:
% 1.20/1.39     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.39       ( ( ?[B:$i]:
% 1.20/1.39           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.20/1.39             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 1.20/1.39         ( v2_funct_1 @ A ) ) ))).
% 1.20/1.39  thf('21', plain,
% 1.20/1.39      (![X14 : $i, X15 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X14)
% 1.20/1.39          | ~ (v1_funct_1 @ X14)
% 1.20/1.39          | ((k5_relat_1 @ X15 @ X14) != (k6_relat_1 @ (k1_relat_1 @ X15)))
% 1.20/1.39          | (v2_funct_1 @ X15)
% 1.20/1.39          | ~ (v1_funct_1 @ X15)
% 1.20/1.39          | ~ (v1_relat_1 @ X15))),
% 1.20/1.39      inference('cnf', [status(esa)], [t53_funct_1])).
% 1.20/1.39  thf('22', plain,
% 1.20/1.39      ((((k5_relat_1 @ sk_A @ sk_B)
% 1.20/1.39          != (k6_relat_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 1.20/1.39        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 1.20/1.39        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 1.20/1.39        | (v2_funct_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 1.20/1.39        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 1.20/1.39        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['20', '21'])).
% 1.20/1.39  thf('23', plain,
% 1.20/1.39      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('24', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 1.20/1.39      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.20/1.39  thf('25', plain,
% 1.20/1.39      (((k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) = (k1_relat_1 @ sk_A))),
% 1.20/1.39      inference('sup+', [status(thm)], ['23', '24'])).
% 1.20/1.39  thf('26', plain,
% 1.20/1.39      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf(t37_relat_1, axiom,
% 1.20/1.39    (![A:$i]:
% 1.20/1.39     ( ( v1_relat_1 @ A ) =>
% 1.20/1.39       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 1.20/1.39         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 1.20/1.39  thf('27', plain,
% 1.20/1.39      (![X1 : $i]:
% 1.20/1.39         (((k1_relat_1 @ X1) = (k2_relat_1 @ (k4_relat_1 @ X1)))
% 1.20/1.39          | ~ (v1_relat_1 @ X1))),
% 1.20/1.39      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.20/1.39  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('29', plain,
% 1.20/1.39      (![X8 : $i]:
% 1.20/1.39         (~ (v2_funct_1 @ X8)
% 1.20/1.39          | ((k2_funct_1 @ X8) = (k4_relat_1 @ X8))
% 1.20/1.39          | ~ (v1_funct_1 @ X8)
% 1.20/1.39          | ~ (v1_relat_1 @ X8))),
% 1.20/1.39      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.20/1.39  thf('30', plain,
% 1.20/1.39      ((~ (v1_funct_1 @ sk_A)
% 1.20/1.39        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))
% 1.20/1.39        | ~ (v2_funct_1 @ sk_A))),
% 1.20/1.39      inference('sup-', [status(thm)], ['28', '29'])).
% 1.20/1.39  thf('31', plain, ((v1_funct_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('32', plain, ((v2_funct_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('33', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.20/1.39  thf(dt_k2_funct_1, axiom,
% 1.20/1.39    (![A:$i]:
% 1.20/1.39     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.39       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.20/1.39         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.20/1.39  thf('34', plain,
% 1.20/1.39      (![X9 : $i]:
% 1.20/1.39         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 1.20/1.39          | ~ (v1_funct_1 @ X9)
% 1.20/1.39          | ~ (v1_relat_1 @ X9))),
% 1.20/1.39      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.39  thf('35', plain,
% 1.20/1.39      (![X9 : $i]:
% 1.20/1.39         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.20/1.39          | ~ (v1_funct_1 @ X9)
% 1.20/1.39          | ~ (v1_relat_1 @ X9))),
% 1.20/1.39      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.39  thf('36', plain,
% 1.20/1.39      (![X8 : $i]:
% 1.20/1.39         (~ (v2_funct_1 @ X8)
% 1.20/1.39          | ((k2_funct_1 @ X8) = (k4_relat_1 @ X8))
% 1.20/1.39          | ~ (v1_funct_1 @ X8)
% 1.20/1.39          | ~ (v1_relat_1 @ X8))),
% 1.20/1.39      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.20/1.39  thf('37', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X0)
% 1.20/1.39          | ~ (v1_funct_1 @ X0)
% 1.20/1.39          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.39          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.39              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 1.20/1.39          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['35', '36'])).
% 1.20/1.39  thf('38', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X0)
% 1.20/1.39          | ~ (v1_funct_1 @ X0)
% 1.20/1.39          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.39          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.39              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 1.20/1.39          | ~ (v1_funct_1 @ X0)
% 1.20/1.39          | ~ (v1_relat_1 @ X0))),
% 1.20/1.39      inference('sup-', [status(thm)], ['34', '37'])).
% 1.20/1.39  thf('39', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 1.20/1.39          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.39          | ~ (v1_funct_1 @ X0)
% 1.20/1.39          | ~ (v1_relat_1 @ X0))),
% 1.20/1.39      inference('simplify', [status(thm)], ['38'])).
% 1.20/1.39  thf('40', plain,
% 1.20/1.39      ((~ (v2_funct_1 @ (k4_relat_1 @ sk_A))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_A)
% 1.20/1.39        | ~ (v1_funct_1 @ sk_A)
% 1.20/1.39        | ((k2_funct_1 @ (k2_funct_1 @ sk_A))
% 1.20/1.39            = (k4_relat_1 @ (k2_funct_1 @ sk_A))))),
% 1.20/1.39      inference('sup-', [status(thm)], ['33', '39'])).
% 1.20/1.39  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('42', plain, ((v1_funct_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('43', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.20/1.39  thf('44', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.20/1.39  thf('45', plain,
% 1.20/1.39      ((~ (v2_funct_1 @ (k4_relat_1 @ sk_A))
% 1.20/1.39        | ((k2_funct_1 @ (k4_relat_1 @ sk_A))
% 1.20/1.39            = (k4_relat_1 @ (k4_relat_1 @ sk_A))))),
% 1.20/1.39      inference('demod', [status(thm)], ['40', '41', '42', '43', '44'])).
% 1.20/1.39  thf('46', plain,
% 1.20/1.39      (![X1 : $i]:
% 1.20/1.39         (((k1_relat_1 @ X1) = (k2_relat_1 @ (k4_relat_1 @ X1)))
% 1.20/1.39          | ~ (v1_relat_1 @ X1))),
% 1.20/1.39      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.20/1.39  thf('47', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.20/1.39  thf(t61_funct_1, axiom,
% 1.20/1.39    (![A:$i]:
% 1.20/1.39     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.39       ( ( v2_funct_1 @ A ) =>
% 1.20/1.39         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.20/1.39             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.20/1.39           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.20/1.39             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.20/1.39  thf('48', plain,
% 1.20/1.39      (![X16 : $i]:
% 1.20/1.39         (~ (v2_funct_1 @ X16)
% 1.20/1.39          | ((k5_relat_1 @ (k2_funct_1 @ X16) @ X16)
% 1.20/1.39              = (k6_relat_1 @ (k2_relat_1 @ X16)))
% 1.20/1.39          | ~ (v1_funct_1 @ X16)
% 1.20/1.39          | ~ (v1_relat_1 @ X16))),
% 1.20/1.39      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.20/1.39  thf('49', plain,
% 1.20/1.39      ((((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 1.20/1.39          = (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_A)
% 1.20/1.39        | ~ (v1_funct_1 @ sk_A)
% 1.20/1.39        | ~ (v2_funct_1 @ sk_A))),
% 1.20/1.39      inference('sup+', [status(thm)], ['47', '48'])).
% 1.20/1.39  thf('50', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('51', plain, ((v1_relat_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('52', plain, ((v1_funct_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('53', plain, ((v2_funct_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('54', plain,
% 1.20/1.39      (((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 1.20/1.39         = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 1.20/1.39      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 1.20/1.39  thf(t48_funct_1, axiom,
% 1.20/1.39    (![A:$i]:
% 1.20/1.39     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.39       ( ![B:$i]:
% 1.20/1.39         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.20/1.39           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.20/1.39               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 1.20/1.39             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 1.20/1.39  thf('55', plain,
% 1.20/1.39      (![X12 : $i, X13 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X12)
% 1.20/1.39          | ~ (v1_funct_1 @ X12)
% 1.20/1.39          | (v2_funct_1 @ X12)
% 1.20/1.39          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X13))
% 1.20/1.39          | ~ (v2_funct_1 @ (k5_relat_1 @ X12 @ X13))
% 1.20/1.39          | ~ (v1_funct_1 @ X13)
% 1.20/1.39          | ~ (v1_relat_1 @ X13))),
% 1.20/1.39      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.20/1.39  thf('56', plain,
% 1.20/1.39      ((~ (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_A)
% 1.20/1.39        | ~ (v1_funct_1 @ sk_A)
% 1.20/1.39        | ((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))
% 1.20/1.39        | (v2_funct_1 @ (k4_relat_1 @ sk_A))
% 1.20/1.39        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 1.20/1.39        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['54', '55'])).
% 1.20/1.39  thf('57', plain, ((v1_relat_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('58', plain, ((v1_funct_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('59', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.20/1.39  thf('60', plain,
% 1.20/1.39      (![X9 : $i]:
% 1.20/1.39         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 1.20/1.39          | ~ (v1_funct_1 @ X9)
% 1.20/1.39          | ~ (v1_relat_1 @ X9))),
% 1.20/1.39      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.39  thf('61', plain,
% 1.20/1.39      (((v1_funct_1 @ (k4_relat_1 @ sk_A))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_A)
% 1.20/1.39        | ~ (v1_funct_1 @ sk_A))),
% 1.20/1.39      inference('sup+', [status(thm)], ['59', '60'])).
% 1.20/1.39  thf('62', plain, ((v1_relat_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('63', plain, ((v1_funct_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('64', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['61', '62', '63'])).
% 1.20/1.39  thf('65', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.20/1.39  thf('66', plain,
% 1.20/1.39      (![X9 : $i]:
% 1.20/1.39         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.20/1.39          | ~ (v1_funct_1 @ X9)
% 1.20/1.39          | ~ (v1_relat_1 @ X9))),
% 1.20/1.39      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.39  thf('67', plain,
% 1.20/1.39      (((v1_relat_1 @ (k4_relat_1 @ sk_A))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_A)
% 1.20/1.39        | ~ (v1_funct_1 @ sk_A))),
% 1.20/1.39      inference('sup+', [status(thm)], ['65', '66'])).
% 1.20/1.39  thf('68', plain, ((v1_relat_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('69', plain, ((v1_funct_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('70', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.20/1.39  thf('71', plain,
% 1.20/1.39      ((~ (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 1.20/1.39        | ((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))
% 1.20/1.39        | (v2_funct_1 @ (k4_relat_1 @ sk_A)))),
% 1.20/1.39      inference('demod', [status(thm)], ['56', '57', '58', '64', '70'])).
% 1.20/1.39  thf('72', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('73', plain,
% 1.20/1.39      (![X7 : $i]:
% 1.20/1.39         (((k5_relat_1 @ X7 @ (k6_relat_1 @ (k2_relat_1 @ X7))) = (X7))
% 1.20/1.39          | ~ (v1_relat_1 @ X7))),
% 1.20/1.39      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.20/1.39  thf('74', plain,
% 1.20/1.39      ((((k5_relat_1 @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B))) = (sk_A))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_A))),
% 1.20/1.39      inference('sup+', [status(thm)], ['72', '73'])).
% 1.20/1.39  thf('75', plain, ((v1_relat_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('76', plain,
% 1.20/1.39      (((k5_relat_1 @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B))) = (sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['74', '75'])).
% 1.20/1.39  thf('77', plain,
% 1.20/1.39      (![X12 : $i, X13 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X12)
% 1.20/1.39          | ~ (v1_funct_1 @ X12)
% 1.20/1.39          | (v2_funct_1 @ X13)
% 1.20/1.39          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X13))
% 1.20/1.39          | ~ (v2_funct_1 @ (k5_relat_1 @ X12 @ X13))
% 1.20/1.39          | ~ (v1_funct_1 @ X13)
% 1.20/1.39          | ~ (v1_relat_1 @ X13))),
% 1.20/1.39      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.20/1.39  thf('78', plain,
% 1.20/1.39      ((~ (v2_funct_1 @ sk_A)
% 1.20/1.39        | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 1.20/1.39        | ~ (v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 1.20/1.39        | ((k2_relat_1 @ sk_A)
% 1.20/1.39            != (k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B))))
% 1.20/1.39        | (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 1.20/1.39        | ~ (v1_funct_1 @ sk_A)
% 1.20/1.39        | ~ (v1_relat_1 @ sk_A))),
% 1.20/1.39      inference('sup-', [status(thm)], ['76', '77'])).
% 1.20/1.39  thf('79', plain, ((v2_funct_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('80', plain,
% 1.20/1.39      (((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 1.20/1.39         = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 1.20/1.39      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 1.20/1.39  thf('81', plain,
% 1.20/1.39      (![X10 : $i, X11 : $i]:
% 1.20/1.39         (~ (v1_funct_1 @ X10)
% 1.20/1.39          | ~ (v1_relat_1 @ X10)
% 1.20/1.39          | ~ (v1_relat_1 @ X11)
% 1.20/1.39          | ~ (v1_funct_1 @ X11)
% 1.20/1.39          | (v1_relat_1 @ (k5_relat_1 @ X10 @ X11)))),
% 1.20/1.39      inference('cnf', [status(esa)], [fc2_funct_1])).
% 1.20/1.39  thf('82', plain,
% 1.20/1.39      (((v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 1.20/1.39        | ~ (v1_funct_1 @ sk_A)
% 1.20/1.39        | ~ (v1_relat_1 @ sk_A)
% 1.20/1.39        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 1.20/1.39        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A)))),
% 1.20/1.39      inference('sup+', [status(thm)], ['80', '81'])).
% 1.20/1.39  thf('83', plain, ((v1_funct_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('84', plain, ((v1_relat_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('85', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.20/1.39  thf('86', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['61', '62', '63'])).
% 1.20/1.39  thf('87', plain, ((v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 1.20/1.39      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 1.20/1.39  thf('88', plain,
% 1.20/1.39      (((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 1.20/1.39         = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 1.20/1.39      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 1.20/1.39  thf('89', plain,
% 1.20/1.39      (![X10 : $i, X11 : $i]:
% 1.20/1.39         (~ (v1_funct_1 @ X10)
% 1.20/1.39          | ~ (v1_relat_1 @ X10)
% 1.20/1.39          | ~ (v1_relat_1 @ X11)
% 1.20/1.39          | ~ (v1_funct_1 @ X11)
% 1.20/1.39          | (v1_funct_1 @ (k5_relat_1 @ X10 @ X11)))),
% 1.20/1.39      inference('cnf', [status(esa)], [fc2_funct_1])).
% 1.20/1.39  thf('90', plain,
% 1.20/1.39      (((v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 1.20/1.39        | ~ (v1_funct_1 @ sk_A)
% 1.20/1.39        | ~ (v1_relat_1 @ sk_A)
% 1.20/1.39        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 1.20/1.39        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A)))),
% 1.20/1.39      inference('sup+', [status(thm)], ['88', '89'])).
% 1.20/1.39  thf('91', plain, ((v1_funct_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('92', plain, ((v1_relat_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('93', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.20/1.39  thf('94', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['61', '62', '63'])).
% 1.20/1.39  thf('95', plain, ((v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 1.20/1.39      inference('demod', [status(thm)], ['90', '91', '92', '93', '94'])).
% 1.20/1.39  thf('96', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('97', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 1.20/1.39      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.20/1.39  thf('98', plain, ((v1_funct_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('99', plain, ((v1_relat_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('100', plain,
% 1.20/1.39      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 1.20/1.39        | (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B))))),
% 1.20/1.39      inference('demod', [status(thm)],
% 1.20/1.39                ['78', '79', '87', '95', '96', '97', '98', '99'])).
% 1.20/1.39  thf('101', plain, ((v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 1.20/1.39      inference('simplify', [status(thm)], ['100'])).
% 1.20/1.39  thf('102', plain,
% 1.20/1.39      ((((k2_relat_1 @ (k4_relat_1 @ sk_A)) != (k1_relat_1 @ sk_A))
% 1.20/1.39        | (v2_funct_1 @ (k4_relat_1 @ sk_A)))),
% 1.20/1.39      inference('demod', [status(thm)], ['71', '101'])).
% 1.20/1.39  thf('103', plain,
% 1.20/1.39      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_A)
% 1.20/1.39        | (v2_funct_1 @ (k4_relat_1 @ sk_A)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['46', '102'])).
% 1.20/1.39  thf('104', plain, ((v1_relat_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('105', plain,
% 1.20/1.39      ((((k1_relat_1 @ sk_A) != (k1_relat_1 @ sk_A))
% 1.20/1.39        | (v2_funct_1 @ (k4_relat_1 @ sk_A)))),
% 1.20/1.39      inference('demod', [status(thm)], ['103', '104'])).
% 1.20/1.39  thf('106', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('simplify', [status(thm)], ['105'])).
% 1.20/1.39  thf('107', plain,
% 1.20/1.39      (((k2_funct_1 @ (k4_relat_1 @ sk_A)) = (k4_relat_1 @ (k4_relat_1 @ sk_A)))),
% 1.20/1.39      inference('demod', [status(thm)], ['45', '106'])).
% 1.20/1.39  thf('108', plain,
% 1.20/1.39      (![X16 : $i]:
% 1.20/1.39         (~ (v2_funct_1 @ X16)
% 1.20/1.39          | ((k5_relat_1 @ (k2_funct_1 @ X16) @ X16)
% 1.20/1.39              = (k6_relat_1 @ (k2_relat_1 @ X16)))
% 1.20/1.39          | ~ (v1_funct_1 @ X16)
% 1.20/1.39          | ~ (v1_relat_1 @ X16))),
% 1.20/1.39      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.20/1.39  thf('109', plain,
% 1.20/1.39      ((((k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_A)) @ (k4_relat_1 @ sk_A))
% 1.20/1.39          = (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A))))
% 1.20/1.39        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 1.20/1.39        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 1.20/1.39        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_A)))),
% 1.20/1.39      inference('sup+', [status(thm)], ['107', '108'])).
% 1.20/1.39  thf('110', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.20/1.39  thf('111', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['61', '62', '63'])).
% 1.20/1.39  thf('112', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('simplify', [status(thm)], ['105'])).
% 1.20/1.39  thf('113', plain,
% 1.20/1.39      (((k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_A)) @ (k4_relat_1 @ sk_A))
% 1.20/1.39         = (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A))))),
% 1.20/1.39      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 1.20/1.39  thf('114', plain,
% 1.20/1.39      (![X10 : $i, X11 : $i]:
% 1.20/1.39         (~ (v1_funct_1 @ X10)
% 1.20/1.39          | ~ (v1_relat_1 @ X10)
% 1.20/1.39          | ~ (v1_relat_1 @ X11)
% 1.20/1.39          | ~ (v1_funct_1 @ X11)
% 1.20/1.39          | (v1_funct_1 @ (k5_relat_1 @ X10 @ X11)))),
% 1.20/1.39      inference('cnf', [status(esa)], [fc2_funct_1])).
% 1.20/1.39  thf('115', plain,
% 1.20/1.39      (((v1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A))))
% 1.20/1.39        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A))
% 1.20/1.39        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 1.20/1.39        | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_A)))
% 1.20/1.39        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_A))))),
% 1.20/1.39      inference('sup+', [status(thm)], ['113', '114'])).
% 1.20/1.39  thf('116', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['61', '62', '63'])).
% 1.20/1.39  thf('117', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.20/1.39  thf('118', plain,
% 1.20/1.39      (((k2_funct_1 @ (k4_relat_1 @ sk_A)) = (k4_relat_1 @ (k4_relat_1 @ sk_A)))),
% 1.20/1.39      inference('demod', [status(thm)], ['45', '106'])).
% 1.20/1.39  thf('119', plain,
% 1.20/1.39      (![X9 : $i]:
% 1.20/1.39         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.20/1.39          | ~ (v1_funct_1 @ X9)
% 1.20/1.39          | ~ (v1_relat_1 @ X9))),
% 1.20/1.39      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.39  thf('120', plain,
% 1.20/1.39      (((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_A)))
% 1.20/1.39        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 1.20/1.39        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A)))),
% 1.20/1.39      inference('sup+', [status(thm)], ['118', '119'])).
% 1.20/1.39  thf('121', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.20/1.39  thf('122', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['61', '62', '63'])).
% 1.20/1.39  thf('123', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_A)))),
% 1.20/1.39      inference('demod', [status(thm)], ['120', '121', '122'])).
% 1.20/1.39  thf('124', plain,
% 1.20/1.39      (((k2_funct_1 @ (k4_relat_1 @ sk_A)) = (k4_relat_1 @ (k4_relat_1 @ sk_A)))),
% 1.20/1.39      inference('demod', [status(thm)], ['45', '106'])).
% 1.20/1.39  thf('125', plain,
% 1.20/1.39      (![X9 : $i]:
% 1.20/1.39         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 1.20/1.39          | ~ (v1_funct_1 @ X9)
% 1.20/1.39          | ~ (v1_relat_1 @ X9))),
% 1.20/1.39      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.39  thf('126', plain,
% 1.20/1.39      (((v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_A)))
% 1.20/1.39        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 1.20/1.39        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_A)))),
% 1.20/1.39      inference('sup+', [status(thm)], ['124', '125'])).
% 1.20/1.39  thf('127', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.20/1.39  thf('128', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['61', '62', '63'])).
% 1.20/1.39  thf('129', plain, ((v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_A)))),
% 1.20/1.39      inference('demod', [status(thm)], ['126', '127', '128'])).
% 1.20/1.39  thf('130', plain,
% 1.20/1.39      ((v1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_A))))),
% 1.20/1.39      inference('demod', [status(thm)], ['115', '116', '117', '123', '129'])).
% 1.20/1.39  thf('131', plain,
% 1.20/1.39      (((v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_A))),
% 1.20/1.39      inference('sup+', [status(thm)], ['27', '130'])).
% 1.20/1.39  thf('132', plain,
% 1.20/1.39      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('133', plain, ((v1_relat_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('134', plain, ((v1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B))),
% 1.20/1.39      inference('demod', [status(thm)], ['131', '132', '133'])).
% 1.20/1.39  thf('135', plain, ((v1_funct_1 @ (k5_relat_1 @ sk_A @ sk_B))),
% 1.20/1.39      inference('demod', [status(thm)], ['131', '132', '133'])).
% 1.20/1.39  thf('136', plain,
% 1.20/1.39      ((((k5_relat_1 @ sk_A @ sk_B) != (k5_relat_1 @ sk_A @ sk_B))
% 1.20/1.39        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 1.20/1.39        | (v2_funct_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 1.20/1.39        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 1.20/1.39      inference('demod', [status(thm)], ['22', '25', '26', '134', '135'])).
% 1.20/1.39  thf('137', plain,
% 1.20/1.39      (((v2_funct_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 1.20/1.39        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 1.20/1.39      inference('simplify', [status(thm)], ['136'])).
% 1.20/1.39  thf('138', plain,
% 1.20/1.39      ((~ (v1_funct_1 @ sk_B)
% 1.20/1.39        | ~ (v1_relat_1 @ sk_B)
% 1.20/1.39        | ~ (v1_relat_1 @ sk_A)
% 1.20/1.39        | ~ (v1_funct_1 @ sk_A)
% 1.20/1.39        | (v2_funct_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['6', '137'])).
% 1.20/1.39  thf('139', plain, ((v1_funct_1 @ sk_B)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('140', plain, ((v1_relat_1 @ sk_B)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('141', plain, ((v1_relat_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('142', plain, ((v1_funct_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('143', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_A @ sk_B))),
% 1.20/1.39      inference('demod', [status(thm)], ['138', '139', '140', '141', '142'])).
% 1.20/1.39  thf('144', plain,
% 1.20/1.39      (![X12 : $i, X13 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X12)
% 1.20/1.39          | ~ (v1_funct_1 @ X12)
% 1.20/1.39          | (v2_funct_1 @ X13)
% 1.20/1.39          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X13))
% 1.20/1.39          | ~ (v2_funct_1 @ (k5_relat_1 @ X12 @ X13))
% 1.20/1.39          | ~ (v1_funct_1 @ X13)
% 1.20/1.39          | ~ (v1_relat_1 @ X13))),
% 1.20/1.39      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.20/1.39  thf('145', plain,
% 1.20/1.39      ((~ (v1_relat_1 @ sk_B)
% 1.20/1.39        | ~ (v1_funct_1 @ sk_B)
% 1.20/1.39        | ((k2_relat_1 @ sk_A) != (k1_relat_1 @ sk_B))
% 1.20/1.39        | (v2_funct_1 @ sk_B)
% 1.20/1.39        | ~ (v1_funct_1 @ sk_A)
% 1.20/1.39        | ~ (v1_relat_1 @ sk_A))),
% 1.20/1.39      inference('sup-', [status(thm)], ['143', '144'])).
% 1.20/1.39  thf('146', plain, ((v1_relat_1 @ sk_B)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('147', plain, ((v1_funct_1 @ sk_B)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('148', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('149', plain, ((v1_funct_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('150', plain, ((v1_relat_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('151', plain,
% 1.20/1.39      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B)) | (v2_funct_1 @ sk_B))),
% 1.20/1.39      inference('demod', [status(thm)],
% 1.20/1.39                ['145', '146', '147', '148', '149', '150'])).
% 1.20/1.39  thf('152', plain, ((v2_funct_1 @ sk_B)),
% 1.20/1.39      inference('simplify', [status(thm)], ['151'])).
% 1.20/1.39  thf('153', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 1.20/1.39      inference('demod', [status(thm)], ['5', '152'])).
% 1.20/1.39  thf('154', plain,
% 1.20/1.39      (![X16 : $i]:
% 1.20/1.39         (~ (v2_funct_1 @ X16)
% 1.20/1.39          | ((k5_relat_1 @ (k2_funct_1 @ X16) @ X16)
% 1.20/1.39              = (k6_relat_1 @ (k2_relat_1 @ X16)))
% 1.20/1.39          | ~ (v1_funct_1 @ X16)
% 1.20/1.39          | ~ (v1_relat_1 @ X16))),
% 1.20/1.39      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.20/1.39  thf('155', plain,
% 1.20/1.39      ((((k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B)
% 1.20/1.39          = (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_B)
% 1.20/1.39        | ~ (v1_funct_1 @ sk_B)
% 1.20/1.39        | ~ (v2_funct_1 @ sk_B))),
% 1.20/1.39      inference('sup+', [status(thm)], ['153', '154'])).
% 1.20/1.39  thf('156', plain, ((v1_relat_1 @ sk_B)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('157', plain, ((v1_funct_1 @ sk_B)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('158', plain, ((v2_funct_1 @ sk_B)),
% 1.20/1.39      inference('simplify', [status(thm)], ['151'])).
% 1.20/1.39  thf('159', plain,
% 1.20/1.39      (((k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B)
% 1.20/1.39         = (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 1.20/1.39      inference('demod', [status(thm)], ['155', '156', '157', '158'])).
% 1.20/1.39  thf('160', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 1.20/1.39      inference('demod', [status(thm)], ['5', '152'])).
% 1.20/1.39  thf('161', plain,
% 1.20/1.39      (![X16 : $i]:
% 1.20/1.39         (~ (v2_funct_1 @ X16)
% 1.20/1.39          | ((k5_relat_1 @ X16 @ (k2_funct_1 @ X16))
% 1.20/1.39              = (k6_relat_1 @ (k1_relat_1 @ X16)))
% 1.20/1.39          | ~ (v1_funct_1 @ X16)
% 1.20/1.39          | ~ (v1_relat_1 @ X16))),
% 1.20/1.39      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.20/1.39  thf('162', plain,
% 1.20/1.39      ((((k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B))
% 1.20/1.39          = (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_B)
% 1.20/1.39        | ~ (v1_funct_1 @ sk_B)
% 1.20/1.39        | ~ (v2_funct_1 @ sk_B))),
% 1.20/1.39      inference('sup+', [status(thm)], ['160', '161'])).
% 1.20/1.39  thf('163', plain, ((v1_relat_1 @ sk_B)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('164', plain, ((v1_funct_1 @ sk_B)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('165', plain, ((v2_funct_1 @ sk_B)),
% 1.20/1.39      inference('simplify', [status(thm)], ['151'])).
% 1.20/1.39  thf('166', plain,
% 1.20/1.39      (((k5_relat_1 @ sk_B @ (k4_relat_1 @ sk_B))
% 1.20/1.39         = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 1.20/1.39      inference('demod', [status(thm)], ['162', '163', '164', '165'])).
% 1.20/1.39  thf(t55_relat_1, axiom,
% 1.20/1.39    (![A:$i]:
% 1.20/1.39     ( ( v1_relat_1 @ A ) =>
% 1.20/1.39       ( ![B:$i]:
% 1.20/1.39         ( ( v1_relat_1 @ B ) =>
% 1.20/1.39           ( ![C:$i]:
% 1.20/1.39             ( ( v1_relat_1 @ C ) =>
% 1.20/1.39               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.20/1.39                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.20/1.39  thf('167', plain,
% 1.20/1.39      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X2)
% 1.20/1.39          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 1.20/1.39              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 1.20/1.39          | ~ (v1_relat_1 @ X4)
% 1.20/1.39          | ~ (v1_relat_1 @ X3))),
% 1.20/1.39      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.20/1.39  thf('168', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 1.20/1.39            = (k5_relat_1 @ sk_B @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0)))
% 1.20/1.39          | ~ (v1_relat_1 @ sk_B)
% 1.20/1.39          | ~ (v1_relat_1 @ X0)
% 1.20/1.39          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 1.20/1.39      inference('sup+', [status(thm)], ['166', '167'])).
% 1.20/1.39  thf('169', plain, ((v1_relat_1 @ sk_B)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('170', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 1.20/1.39      inference('demod', [status(thm)], ['5', '152'])).
% 1.20/1.39  thf('171', plain,
% 1.20/1.39      (![X9 : $i]:
% 1.20/1.39         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.20/1.39          | ~ (v1_funct_1 @ X9)
% 1.20/1.39          | ~ (v1_relat_1 @ X9))),
% 1.20/1.39      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.39  thf('172', plain,
% 1.20/1.39      (((v1_relat_1 @ (k4_relat_1 @ sk_B))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_B)
% 1.20/1.39        | ~ (v1_funct_1 @ sk_B))),
% 1.20/1.39      inference('sup+', [status(thm)], ['170', '171'])).
% 1.20/1.39  thf('173', plain, ((v1_relat_1 @ sk_B)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('174', plain, ((v1_funct_1 @ sk_B)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('175', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 1.20/1.39      inference('demod', [status(thm)], ['172', '173', '174'])).
% 1.20/1.39  thf('176', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 1.20/1.39            = (k5_relat_1 @ sk_B @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ X0)))
% 1.20/1.39          | ~ (v1_relat_1 @ X0))),
% 1.20/1.39      inference('demod', [status(thm)], ['168', '169', '175'])).
% 1.20/1.39  thf('177', plain,
% 1.20/1.39      ((((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B)
% 1.20/1.39          = (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_B))),
% 1.20/1.39      inference('sup+', [status(thm)], ['159', '176'])).
% 1.20/1.39  thf('178', plain,
% 1.20/1.39      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('179', plain,
% 1.20/1.39      (![X1 : $i]:
% 1.20/1.39         (((k1_relat_1 @ X1) = (k2_relat_1 @ (k4_relat_1 @ X1)))
% 1.20/1.39          | ~ (v1_relat_1 @ X1))),
% 1.20/1.39      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.20/1.39  thf('180', plain,
% 1.20/1.39      (![X7 : $i]:
% 1.20/1.39         (((k5_relat_1 @ X7 @ (k6_relat_1 @ (k2_relat_1 @ X7))) = (X7))
% 1.20/1.39          | ~ (v1_relat_1 @ X7))),
% 1.20/1.39      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.20/1.39  thf('181', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (((k5_relat_1 @ (k4_relat_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.20/1.39            = (k4_relat_1 @ X0))
% 1.20/1.39          | ~ (v1_relat_1 @ X0)
% 1.20/1.39          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 1.20/1.39      inference('sup+', [status(thm)], ['179', '180'])).
% 1.20/1.39  thf(dt_k4_relat_1, axiom,
% 1.20/1.39    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 1.20/1.39  thf('182', plain,
% 1.20/1.39      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 1.20/1.39      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.20/1.39  thf('183', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X0)
% 1.20/1.39          | ((k5_relat_1 @ (k4_relat_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.20/1.39              = (k4_relat_1 @ X0)))),
% 1.20/1.39      inference('clc', [status(thm)], ['181', '182'])).
% 1.20/1.39  thf('184', plain,
% 1.20/1.39      ((((k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B))
% 1.20/1.39          = (k4_relat_1 @ sk_A))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_A))),
% 1.20/1.39      inference('sup+', [status(thm)], ['178', '183'])).
% 1.20/1.39  thf('185', plain, ((v1_relat_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('186', plain,
% 1.20/1.39      (((k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B))
% 1.20/1.39         = (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['184', '185'])).
% 1.20/1.39  thf('187', plain,
% 1.20/1.39      (((k5_relat_1 @ (k4_relat_1 @ sk_A) @ sk_A)
% 1.20/1.39         = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 1.20/1.39      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 1.20/1.39  thf('188', plain,
% 1.20/1.39      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X2)
% 1.20/1.39          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 1.20/1.39              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 1.20/1.39          | ~ (v1_relat_1 @ X4)
% 1.20/1.39          | ~ (v1_relat_1 @ X3))),
% 1.20/1.39      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.20/1.39  thf('189', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 1.20/1.39            = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 1.20/1.39          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_A))
% 1.20/1.39          | ~ (v1_relat_1 @ X0)
% 1.20/1.39          | ~ (v1_relat_1 @ sk_A))),
% 1.20/1.39      inference('sup+', [status(thm)], ['187', '188'])).
% 1.20/1.39  thf('190', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.20/1.39  thf('191', plain, ((v1_relat_1 @ sk_A)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('192', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 1.20/1.39            = (k5_relat_1 @ (k4_relat_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 1.20/1.39          | ~ (v1_relat_1 @ X0))),
% 1.20/1.39      inference('demod', [status(thm)], ['189', '190', '191'])).
% 1.20/1.39  thf('193', plain,
% 1.20/1.39      ((((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B)
% 1.20/1.39          = (k4_relat_1 @ sk_A))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_B))),
% 1.20/1.39      inference('sup+', [status(thm)], ['186', '192'])).
% 1.20/1.39  thf('194', plain, ((v1_relat_1 @ sk_B)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('195', plain,
% 1.20/1.39      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B)
% 1.20/1.39         = (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['193', '194'])).
% 1.20/1.39  thf('196', plain, ((v1_relat_1 @ sk_B)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('197', plain,
% 1.20/1.39      (((k4_relat_1 @ sk_A)
% 1.20/1.39         = (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 1.20/1.39      inference('demod', [status(thm)], ['177', '195', '196'])).
% 1.20/1.39  thf('198', plain, ((((k4_relat_1 @ sk_A) = (sk_B)) | ~ (v1_relat_1 @ sk_B))),
% 1.20/1.39      inference('sup+', [status(thm)], ['0', '197'])).
% 1.20/1.39  thf('199', plain, ((v1_relat_1 @ sk_B)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('200', plain, (((k4_relat_1 @ sk_A) = (sk_B))),
% 1.20/1.39      inference('demod', [status(thm)], ['198', '199'])).
% 1.20/1.39  thf('201', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('202', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.20/1.39  thf('203', plain, (((sk_B) != (k4_relat_1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['201', '202'])).
% 1.20/1.39  thf('204', plain, ($false),
% 1.20/1.39      inference('simplify_reflect-', [status(thm)], ['200', '203'])).
% 1.20/1.39  
% 1.20/1.39  % SZS output end Refutation
% 1.20/1.39  
% 1.20/1.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

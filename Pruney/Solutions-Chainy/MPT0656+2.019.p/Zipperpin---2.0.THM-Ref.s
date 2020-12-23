%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OBjUw7Yt6v

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:39 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 164 expanded)
%              Number of leaves         :   21 (  60 expanded)
%              Depth                    :   26
%              Number of atoms          :  810 (2020 expanded)
%              Number of equality atoms :   59 ( 190 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ X9 @ ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('8',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('9',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('10',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X8 ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

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

thf('14',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('15',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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

thf('16',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('17',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ X9 @ ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22','23','24'])).

thf('26',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('27',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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

thf('30',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X14 ) @ X14 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['28','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A )
    = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['27','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('49',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47','48','49','50','51'])).

thf('53',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_B
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( sk_B
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OBjUw7Yt6v
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:39:18 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.82/1.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.82/1.03  % Solved by: fo/fo7.sh
% 0.82/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.03  % done 611 iterations in 0.589s
% 0.82/1.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.82/1.03  % SZS output start Refutation
% 0.82/1.03  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.82/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.03  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.82/1.03  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.82/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.82/1.03  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.82/1.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.82/1.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.82/1.03  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.82/1.03  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.82/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.82/1.03  thf(t71_relat_1, axiom,
% 0.82/1.03    (![A:$i]:
% 0.82/1.03     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.82/1.03       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.82/1.03  thf('0', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 0.82/1.03      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.82/1.03  thf(t80_relat_1, axiom,
% 0.82/1.03    (![A:$i]:
% 0.82/1.03     ( ( v1_relat_1 @ A ) =>
% 0.82/1.03       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.82/1.03  thf('1', plain,
% 0.82/1.03      (![X9 : $i]:
% 0.82/1.03         (((k5_relat_1 @ X9 @ (k6_relat_1 @ (k2_relat_1 @ X9))) = (X9))
% 0.82/1.03          | ~ (v1_relat_1 @ X9))),
% 0.82/1.03      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.82/1.03  thf('2', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.82/1.03            = (k6_relat_1 @ X0))
% 0.82/1.03          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.82/1.03      inference('sup+', [status(thm)], ['0', '1'])).
% 0.82/1.03  thf(fc4_funct_1, axiom,
% 0.82/1.03    (![A:$i]:
% 0.82/1.03     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.82/1.03       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.82/1.03  thf('3', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.82/1.03      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.82/1.03  thf('4', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.82/1.03           = (k6_relat_1 @ X0))),
% 0.82/1.03      inference('demod', [status(thm)], ['2', '3'])).
% 0.82/1.03  thf(t45_relat_1, axiom,
% 0.82/1.03    (![A:$i]:
% 0.82/1.03     ( ( v1_relat_1 @ A ) =>
% 0.82/1.03       ( ![B:$i]:
% 0.82/1.03         ( ( v1_relat_1 @ B ) =>
% 0.82/1.03           ( r1_tarski @
% 0.82/1.03             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.82/1.03  thf('5', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         (~ (v1_relat_1 @ X0)
% 0.82/1.03          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.82/1.03             (k2_relat_1 @ X0))
% 0.82/1.03          | ~ (v1_relat_1 @ X1))),
% 0.82/1.03      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.82/1.03  thf('6', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         ((r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.82/1.03           (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.82/1.03          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.82/1.03          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.82/1.03      inference('sup+', [status(thm)], ['4', '5'])).
% 0.82/1.03  thf('7', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 0.82/1.03      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.82/1.03  thf('8', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 0.82/1.03      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.82/1.03  thf('9', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.82/1.03      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.82/1.03  thf('10', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.82/1.03      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.82/1.03  thf('11', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.82/1.03      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 0.82/1.03  thf(t77_relat_1, axiom,
% 0.82/1.03    (![A:$i,B:$i]:
% 0.82/1.03     ( ( v1_relat_1 @ B ) =>
% 0.82/1.03       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.82/1.03         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.82/1.03  thf('12', plain,
% 0.82/1.03      (![X7 : $i, X8 : $i]:
% 0.82/1.03         (~ (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.82/1.03          | ((k5_relat_1 @ (k6_relat_1 @ X8) @ X7) = (X7))
% 0.82/1.03          | ~ (v1_relat_1 @ X7))),
% 0.82/1.03      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.82/1.03  thf('13', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (~ (v1_relat_1 @ X0)
% 0.82/1.03          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['11', '12'])).
% 0.82/1.03  thf(t63_funct_1, conjecture,
% 0.82/1.03    (![A:$i]:
% 0.82/1.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.82/1.03       ( ![B:$i]:
% 0.82/1.03         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.82/1.03           ( ( ( v2_funct_1 @ A ) & 
% 0.82/1.03               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.82/1.03               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.82/1.03             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.82/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.03    (~( ![A:$i]:
% 0.82/1.03        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.82/1.03          ( ![B:$i]:
% 0.82/1.03            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.82/1.03              ( ( ( v2_funct_1 @ A ) & 
% 0.82/1.03                  ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.82/1.03                  ( ( k5_relat_1 @ A @ B ) =
% 0.82/1.03                    ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.82/1.03                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.82/1.03    inference('cnf.neg', [status(esa)], [t63_funct_1])).
% 0.82/1.03  thf('14', plain,
% 0.82/1.03      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(dt_k2_funct_1, axiom,
% 0.82/1.03    (![A:$i]:
% 0.82/1.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.82/1.03       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.82/1.03         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.82/1.03  thf('15', plain,
% 0.82/1.03      (![X10 : $i]:
% 0.82/1.03         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.82/1.03          | ~ (v1_funct_1 @ X10)
% 0.82/1.03          | ~ (v1_relat_1 @ X10))),
% 0.82/1.03      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.82/1.03  thf(t55_funct_1, axiom,
% 0.82/1.03    (![A:$i]:
% 0.82/1.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.82/1.03       ( ( v2_funct_1 @ A ) =>
% 0.82/1.03         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.82/1.03           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.82/1.03  thf('16', plain,
% 0.82/1.03      (![X13 : $i]:
% 0.82/1.03         (~ (v2_funct_1 @ X13)
% 0.82/1.03          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 0.82/1.03          | ~ (v1_funct_1 @ X13)
% 0.82/1.03          | ~ (v1_relat_1 @ X13))),
% 0.82/1.03      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.82/1.03  thf('17', plain,
% 0.82/1.03      (![X9 : $i]:
% 0.82/1.03         (((k5_relat_1 @ X9 @ (k6_relat_1 @ (k2_relat_1 @ X9))) = (X9))
% 0.82/1.03          | ~ (v1_relat_1 @ X9))),
% 0.82/1.03      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.82/1.03  thf('18', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.82/1.03            = (k2_funct_1 @ X0))
% 0.82/1.03          | ~ (v1_relat_1 @ X0)
% 0.82/1.03          | ~ (v1_funct_1 @ X0)
% 0.82/1.03          | ~ (v2_funct_1 @ X0)
% 0.82/1.03          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.82/1.03      inference('sup+', [status(thm)], ['16', '17'])).
% 0.82/1.03  thf('19', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (~ (v1_relat_1 @ X0)
% 0.82/1.03          | ~ (v1_funct_1 @ X0)
% 0.82/1.03          | ~ (v2_funct_1 @ X0)
% 0.82/1.03          | ~ (v1_funct_1 @ X0)
% 0.82/1.03          | ~ (v1_relat_1 @ X0)
% 0.82/1.03          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.82/1.03              = (k2_funct_1 @ X0)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['15', '18'])).
% 0.82/1.03  thf('20', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.82/1.03            = (k2_funct_1 @ X0))
% 0.82/1.03          | ~ (v2_funct_1 @ X0)
% 0.82/1.03          | ~ (v1_funct_1 @ X0)
% 0.82/1.03          | ~ (v1_relat_1 @ X0))),
% 0.82/1.03      inference('simplify', [status(thm)], ['19'])).
% 0.82/1.03  thf('21', plain,
% 0.82/1.03      ((((k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B))
% 0.82/1.03          = (k2_funct_1 @ sk_A))
% 0.82/1.03        | ~ (v1_relat_1 @ sk_A)
% 0.82/1.03        | ~ (v1_funct_1 @ sk_A)
% 0.82/1.03        | ~ (v2_funct_1 @ sk_A))),
% 0.82/1.03      inference('sup+', [status(thm)], ['14', '20'])).
% 0.82/1.03  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('23', plain, ((v1_funct_1 @ sk_A)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('24', plain, ((v2_funct_1 @ sk_A)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('25', plain,
% 0.82/1.03      (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B))
% 0.82/1.03         = (k2_funct_1 @ sk_A))),
% 0.82/1.03      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 0.82/1.03  thf('26', plain,
% 0.82/1.03      (![X10 : $i]:
% 0.82/1.03         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.82/1.03          | ~ (v1_funct_1 @ X10)
% 0.82/1.03          | ~ (v1_relat_1 @ X10))),
% 0.82/1.03      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.82/1.03  thf('27', plain,
% 0.82/1.03      (![X13 : $i]:
% 0.82/1.03         (~ (v2_funct_1 @ X13)
% 0.82/1.03          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 0.82/1.03          | ~ (v1_funct_1 @ X13)
% 0.82/1.03          | ~ (v1_relat_1 @ X13))),
% 0.82/1.03      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.82/1.03  thf('28', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('29', plain,
% 0.82/1.03      (![X10 : $i]:
% 0.82/1.03         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.82/1.03          | ~ (v1_funct_1 @ X10)
% 0.82/1.03          | ~ (v1_relat_1 @ X10))),
% 0.82/1.03      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.82/1.03  thf(t61_funct_1, axiom,
% 0.82/1.03    (![A:$i]:
% 0.82/1.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.82/1.03       ( ( v2_funct_1 @ A ) =>
% 0.82/1.03         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.82/1.03             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.82/1.03           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.82/1.03             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.82/1.03  thf('30', plain,
% 0.82/1.03      (![X14 : $i]:
% 0.82/1.03         (~ (v2_funct_1 @ X14)
% 0.82/1.03          | ((k5_relat_1 @ (k2_funct_1 @ X14) @ X14)
% 0.82/1.03              = (k6_relat_1 @ (k2_relat_1 @ X14)))
% 0.82/1.03          | ~ (v1_funct_1 @ X14)
% 0.82/1.03          | ~ (v1_relat_1 @ X14))),
% 0.82/1.03      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.82/1.03  thf('31', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (~ (v1_relat_1 @ X0)
% 0.82/1.03          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['11', '12'])).
% 0.82/1.03  thf(t55_relat_1, axiom,
% 0.82/1.03    (![A:$i]:
% 0.82/1.03     ( ( v1_relat_1 @ A ) =>
% 0.82/1.03       ( ![B:$i]:
% 0.82/1.03         ( ( v1_relat_1 @ B ) =>
% 0.82/1.03           ( ![C:$i]:
% 0.82/1.03             ( ( v1_relat_1 @ C ) =>
% 0.82/1.03               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.82/1.03                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.82/1.03  thf('32', plain,
% 0.82/1.03      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.82/1.03         (~ (v1_relat_1 @ X2)
% 0.82/1.03          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 0.82/1.03              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 0.82/1.03          | ~ (v1_relat_1 @ X4)
% 0.82/1.03          | ~ (v1_relat_1 @ X3))),
% 0.82/1.03      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.82/1.03  thf('33', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         (((k5_relat_1 @ X0 @ X1)
% 0.82/1.03            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 0.82/1.03               (k5_relat_1 @ X0 @ X1)))
% 0.82/1.03          | ~ (v1_relat_1 @ X0)
% 0.82/1.03          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.82/1.03          | ~ (v1_relat_1 @ X1)
% 0.82/1.03          | ~ (v1_relat_1 @ X0))),
% 0.82/1.03      inference('sup+', [status(thm)], ['31', '32'])).
% 0.82/1.03  thf('34', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.82/1.03      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.82/1.03  thf('35', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         (((k5_relat_1 @ X0 @ X1)
% 0.82/1.03            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 0.82/1.03               (k5_relat_1 @ X0 @ X1)))
% 0.82/1.03          | ~ (v1_relat_1 @ X0)
% 0.82/1.03          | ~ (v1_relat_1 @ X1)
% 0.82/1.03          | ~ (v1_relat_1 @ X0))),
% 0.82/1.03      inference('demod', [status(thm)], ['33', '34'])).
% 0.82/1.03  thf('36', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         (~ (v1_relat_1 @ X1)
% 0.82/1.03          | ~ (v1_relat_1 @ X0)
% 0.82/1.03          | ((k5_relat_1 @ X0 @ X1)
% 0.82/1.03              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 0.82/1.03                 (k5_relat_1 @ X0 @ X1))))),
% 0.82/1.03      inference('simplify', [status(thm)], ['35'])).
% 0.82/1.03  thf('37', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.82/1.03            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 0.82/1.04               (k6_relat_1 @ (k2_relat_1 @ X0))))
% 0.82/1.04          | ~ (v1_relat_1 @ X0)
% 0.82/1.04          | ~ (v1_funct_1 @ X0)
% 0.82/1.04          | ~ (v2_funct_1 @ X0)
% 0.82/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.82/1.04          | ~ (v1_relat_1 @ X0))),
% 0.82/1.04      inference('sup+', [status(thm)], ['30', '36'])).
% 0.82/1.04  thf('38', plain,
% 0.82/1.04      (![X0 : $i]:
% 0.82/1.04         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.82/1.04          | ~ (v2_funct_1 @ X0)
% 0.82/1.04          | ~ (v1_funct_1 @ X0)
% 0.82/1.04          | ~ (v1_relat_1 @ X0)
% 0.82/1.04          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.82/1.04              = (k5_relat_1 @ 
% 0.82/1.04                 (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 0.82/1.04                 (k6_relat_1 @ (k2_relat_1 @ X0)))))),
% 0.82/1.04      inference('simplify', [status(thm)], ['37'])).
% 0.82/1.04  thf('39', plain,
% 0.82/1.04      (![X0 : $i]:
% 0.82/1.04         (~ (v1_relat_1 @ X0)
% 0.82/1.04          | ~ (v1_funct_1 @ X0)
% 0.82/1.04          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.82/1.04              = (k5_relat_1 @ 
% 0.82/1.04                 (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 0.82/1.04                 (k6_relat_1 @ (k2_relat_1 @ X0))))
% 0.82/1.04          | ~ (v1_relat_1 @ X0)
% 0.82/1.04          | ~ (v1_funct_1 @ X0)
% 0.82/1.04          | ~ (v2_funct_1 @ X0))),
% 0.82/1.04      inference('sup-', [status(thm)], ['29', '38'])).
% 0.82/1.04  thf('40', plain,
% 0.82/1.04      (![X0 : $i]:
% 0.82/1.04         (~ (v2_funct_1 @ X0)
% 0.82/1.04          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.82/1.04              = (k5_relat_1 @ 
% 0.82/1.04                 (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 0.82/1.04                 (k6_relat_1 @ (k2_relat_1 @ X0))))
% 0.82/1.04          | ~ (v1_funct_1 @ X0)
% 0.82/1.04          | ~ (v1_relat_1 @ X0))),
% 0.82/1.04      inference('simplify', [status(thm)], ['39'])).
% 0.82/1.04  thf('41', plain,
% 0.82/1.04      ((((k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A)
% 0.82/1.04          = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_A))) @ 
% 0.82/1.04             (k6_relat_1 @ (k1_relat_1 @ sk_B))))
% 0.82/1.04        | ~ (v1_relat_1 @ sk_A)
% 0.82/1.04        | ~ (v1_funct_1 @ sk_A)
% 0.82/1.04        | ~ (v2_funct_1 @ sk_A))),
% 0.82/1.04      inference('sup+', [status(thm)], ['28', '40'])).
% 0.82/1.04  thf('42', plain, ((v1_relat_1 @ sk_A)),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('43', plain, ((v1_funct_1 @ sk_A)),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('44', plain, ((v2_funct_1 @ sk_A)),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('45', plain,
% 0.82/1.04      (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A)
% 0.82/1.04         = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_A))) @ 
% 0.82/1.04            (k6_relat_1 @ (k1_relat_1 @ sk_B))))),
% 0.82/1.04      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.82/1.04  thf('46', plain,
% 0.82/1.04      ((((k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A)
% 0.82/1.04          = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ 
% 0.82/1.04             (k6_relat_1 @ (k1_relat_1 @ sk_B))))
% 0.82/1.04        | ~ (v1_relat_1 @ sk_A)
% 0.82/1.04        | ~ (v1_funct_1 @ sk_A)
% 0.82/1.04        | ~ (v2_funct_1 @ sk_A))),
% 0.82/1.04      inference('sup+', [status(thm)], ['27', '45'])).
% 0.82/1.04  thf('47', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('48', plain,
% 0.82/1.04      (![X0 : $i]:
% 0.82/1.04         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.82/1.04           = (k6_relat_1 @ X0))),
% 0.82/1.04      inference('demod', [status(thm)], ['2', '3'])).
% 0.82/1.04  thf('49', plain, ((v1_relat_1 @ sk_A)),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('50', plain, ((v1_funct_1 @ sk_A)),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('51', plain, ((v2_funct_1 @ sk_A)),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('52', plain,
% 0.82/1.04      (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A)
% 0.82/1.04         = (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 0.82/1.04      inference('demod', [status(thm)], ['46', '47', '48', '49', '50', '51'])).
% 0.82/1.04  thf('53', plain,
% 0.82/1.04      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.82/1.04         (~ (v1_relat_1 @ X2)
% 0.82/1.04          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 0.82/1.04              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 0.82/1.04          | ~ (v1_relat_1 @ X4)
% 0.82/1.04          | ~ (v1_relat_1 @ X3))),
% 0.82/1.04      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.82/1.04  thf('54', plain,
% 0.82/1.04      (![X0 : $i]:
% 0.82/1.04         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.82/1.04            = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 0.82/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.82/1.04          | ~ (v1_relat_1 @ X0)
% 0.82/1.04          | ~ (v1_relat_1 @ sk_A))),
% 0.82/1.04      inference('sup+', [status(thm)], ['52', '53'])).
% 0.82/1.04  thf('55', plain, ((v1_relat_1 @ sk_A)),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('56', plain,
% 0.82/1.04      (![X0 : $i]:
% 0.82/1.04         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.82/1.04            = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 0.82/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 0.82/1.04          | ~ (v1_relat_1 @ X0))),
% 0.82/1.04      inference('demod', [status(thm)], ['54', '55'])).
% 0.82/1.04  thf('57', plain,
% 0.82/1.04      (![X0 : $i]:
% 0.82/1.04         (~ (v1_relat_1 @ sk_A)
% 0.82/1.04          | ~ (v1_funct_1 @ sk_A)
% 0.82/1.04          | ~ (v1_relat_1 @ X0)
% 0.82/1.04          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.82/1.04              = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0))))),
% 0.82/1.04      inference('sup-', [status(thm)], ['26', '56'])).
% 0.82/1.04  thf('58', plain, ((v1_relat_1 @ sk_A)),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('59', plain, ((v1_funct_1 @ sk_A)),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('60', plain,
% 0.82/1.04      (![X0 : $i]:
% 0.82/1.04         (~ (v1_relat_1 @ X0)
% 0.82/1.04          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 0.82/1.04              = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0))))),
% 0.82/1.04      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.82/1.04  thf('61', plain,
% 0.82/1.04      ((((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B)
% 0.82/1.04          = (k2_funct_1 @ sk_A))
% 0.82/1.04        | ~ (v1_relat_1 @ sk_B))),
% 0.82/1.04      inference('sup+', [status(thm)], ['25', '60'])).
% 0.82/1.04  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('63', plain,
% 0.82/1.04      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B)
% 0.82/1.04         = (k2_funct_1 @ sk_A))),
% 0.82/1.04      inference('demod', [status(thm)], ['61', '62'])).
% 0.82/1.04  thf('64', plain, ((((sk_B) = (k2_funct_1 @ sk_A)) | ~ (v1_relat_1 @ sk_B))),
% 0.82/1.04      inference('sup+', [status(thm)], ['13', '63'])).
% 0.82/1.04  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('66', plain, (((sk_B) = (k2_funct_1 @ sk_A))),
% 0.82/1.04      inference('demod', [status(thm)], ['64', '65'])).
% 0.82/1.04  thf('67', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('68', plain, ($false),
% 0.82/1.04      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 0.82/1.04  
% 0.82/1.04  % SZS output end Refutation
% 0.82/1.04  
% 0.82/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

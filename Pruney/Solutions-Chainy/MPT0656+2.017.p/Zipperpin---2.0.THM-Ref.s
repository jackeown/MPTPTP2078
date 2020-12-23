%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eFNsTyRlhC

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:38 EST 2020

% Result     : Theorem 2.06s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  307 (2540 expanded)
%              Number of leaves         :   25 ( 812 expanded)
%              Depth                    :   31
%              Number of atoms          : 2670 (31752 expanded)
%              Number of equality atoms :  151 (2643 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k1_relat_1 @ X2 ) )
        = ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('2',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('4',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k9_relat_1 @ X3 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('6',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','13'])).

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
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X19 ) @ X19 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('16',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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

thf('18',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relat_1 @ X18 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('19',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
      = ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['16','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','13'])).

thf('29',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('36',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('37',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('38',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('42',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('45',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('46',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('47',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('49',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X13 ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('52',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','55'])).

thf('57',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('58',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('59',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['34','65'])).

thf('67',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('68',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('70',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('71',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('72',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','75'])).

thf('77',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['68','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('85',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X13 ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_A ) )
      = ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_A ) )
      = ( k2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_A ) )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['66','90','91','92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','94'])).

thf('96',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('98',plain,
    ( ( ( k5_relat_1 @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k5_relat_1 @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('102',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('105',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['106','110'])).

thf('112',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('113',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('121',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['116','122'])).

thf('124',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['115','125'])).

thf('127',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['100','129'])).

thf('131',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k9_relat_1 @ X3 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('134',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_A ) @ ( k6_relat_1 @ ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['132','135'])).

thf('137',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('139',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_A ) @ ( k6_relat_1 @ ( k9_relat_1 @ sk_A @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['136','137','138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_A ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k9_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('144',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,
    ( ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['95','145'])).

thf('147',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['66','90','91','92','93'])).

thf('149',plain,(
    v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('151',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) @ ( k6_relat_1 @ ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['66','90','91','92','93'])).

thf('154',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relat_1 @ X18 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('155',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('156',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('157',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k9_relat_1 @ X3 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('158',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('160',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['155','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) )
    = ( k9_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['161','162','163'])).

thf('165',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['154','164'])).

thf('166',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('167',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('168',plain,(
    ! [X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k1_relat_1 @ X2 ) )
        = ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('171',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['165','166','172','173','174','175'])).

thf('177',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('178',plain,(
    ! [X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k1_relat_1 @ X2 ) )
        = ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('179',plain,
    ( ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('180',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( k9_relat_1 @ sk_A @ ( k2_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,
    ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['151','152','153','176','182'])).

thf('184',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','183'])).

thf('185',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('187',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['184','185','186','187','188','189'])).

thf('191',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['190','191'])).

thf('193',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['66','90','91','92','93'])).

thf('194',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['192','193','194'])).

thf('196',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('198',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('199',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ X19 @ ( k2_funct_1 @ X19 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('200',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('202',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ sk_A )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['200','201'])).

thf('203',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('208',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['206','207','208'])).

thf('210',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('211',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['212','213'])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['209','215'])).

thf('217',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,
    ( ( k5_relat_1 @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['98','99'])).

thf('220',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
        = ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['219','220'])).

thf('222',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
        = ( k5_relat_1 @ sk_A @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['221','222','223'])).

thf('225',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['224','225'])).

thf('227',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('228',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['226','227','228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['218','230'])).

thf('232',plain,
    ( ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['199','231'])).

thf('233',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('234',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['66','90','91','92','93'])).

thf('238',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['232','233','234','235','236','237'])).

thf('239',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('240',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) @ ( k6_relat_1 @ ( k9_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) ) ) )
      = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('242',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('244',plain,
    ( ( k5_relat_1 @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['240','241','242','243'])).

thf('245',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['244','245'])).

thf('247',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['232','233','234','235','236','237'])).

thf('248',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['246','247'])).

thf('249',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['198','248'])).

thf('250',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) @ ( k6_relat_1 @ ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('256',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('257',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) @ ( k6_relat_1 @ ( k9_relat_1 @ sk_B @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['253','254','255','256'])).

thf('258',plain,
    ( ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['197','257'])).

thf('259',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k9_relat_1 @ X3 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('260',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('261',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
      = ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['259','260'])).

thf('262',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['261','262','263','264'])).

thf('266',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('267',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['265','266'])).

thf('268',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,
    ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['258','267','268'])).

thf('270',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('271',plain,
    ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['258','267','268'])).

thf('272',plain,
    ( ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
      = sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['270','271'])).

thf('273',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,
    ( ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['272','273'])).

thf('275',plain,
    ( sk_B
    = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['269','274'])).

thf('276',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('277',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,
    ( sk_B
    = ( k2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['196','275','276','277'])).

thf('279',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['278','279'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eFNsTyRlhC
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.06/2.29  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.06/2.29  % Solved by: fo/fo7.sh
% 2.06/2.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.06/2.29  % done 2080 iterations in 1.833s
% 2.06/2.29  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.06/2.29  % SZS output start Refutation
% 2.06/2.29  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.06/2.29  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.06/2.29  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.06/2.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.06/2.29  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.06/2.29  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.06/2.29  thf(sk_A_type, type, sk_A: $i).
% 2.06/2.29  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.06/2.29  thf(sk_B_type, type, sk_B: $i).
% 2.06/2.29  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.06/2.29  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.06/2.29  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.06/2.29  thf(t63_funct_1, conjecture,
% 2.06/2.29    (![A:$i]:
% 2.06/2.29     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.06/2.29       ( ![B:$i]:
% 2.06/2.29         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.06/2.29           ( ( ( v2_funct_1 @ A ) & 
% 2.06/2.29               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 2.06/2.29               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 2.06/2.29             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.06/2.29  thf(zf_stmt_0, negated_conjecture,
% 2.06/2.29    (~( ![A:$i]:
% 2.06/2.29        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.06/2.29          ( ![B:$i]:
% 2.06/2.29            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.06/2.29              ( ( ( v2_funct_1 @ A ) & 
% 2.06/2.29                  ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 2.06/2.29                  ( ( k5_relat_1 @ A @ B ) =
% 2.06/2.29                    ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 2.06/2.29                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 2.06/2.29    inference('cnf.neg', [status(esa)], [t63_funct_1])).
% 2.06/2.29  thf('0', plain,
% 2.06/2.29      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf(t146_relat_1, axiom,
% 2.06/2.29    (![A:$i]:
% 2.06/2.29     ( ( v1_relat_1 @ A ) =>
% 2.06/2.29       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 2.06/2.29  thf('1', plain,
% 2.06/2.29      (![X2 : $i]:
% 2.06/2.29         (((k9_relat_1 @ X2 @ (k1_relat_1 @ X2)) = (k2_relat_1 @ X2))
% 2.06/2.29          | ~ (v1_relat_1 @ X2))),
% 2.06/2.29      inference('cnf', [status(esa)], [t146_relat_1])).
% 2.06/2.29  thf('2', plain,
% 2.06/2.29      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf(t71_relat_1, axiom,
% 2.06/2.29    (![A:$i]:
% 2.06/2.29     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.06/2.29       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.06/2.29  thf('3', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 2.06/2.29      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.06/2.29  thf('4', plain,
% 2.06/2.29      (((k2_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) = (k1_relat_1 @ sk_A))),
% 2.06/2.29      inference('sup+', [status(thm)], ['2', '3'])).
% 2.06/2.29  thf(t160_relat_1, axiom,
% 2.06/2.29    (![A:$i]:
% 2.06/2.29     ( ( v1_relat_1 @ A ) =>
% 2.06/2.29       ( ![B:$i]:
% 2.06/2.29         ( ( v1_relat_1 @ B ) =>
% 2.06/2.29           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.06/2.29             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.06/2.29  thf('5', plain,
% 2.06/2.29      (![X3 : $i, X4 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X3)
% 2.06/2.29          | ((k2_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 2.06/2.29              = (k9_relat_1 @ X3 @ (k2_relat_1 @ X4)))
% 2.06/2.29          | ~ (v1_relat_1 @ X4))),
% 2.06/2.29      inference('cnf', [status(esa)], [t160_relat_1])).
% 2.06/2.29  thf('6', plain,
% 2.06/2.29      ((((k1_relat_1 @ sk_A) = (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 2.06/2.29        | ~ (v1_relat_1 @ sk_A)
% 2.06/2.29        | ~ (v1_relat_1 @ sk_B))),
% 2.06/2.29      inference('sup+', [status(thm)], ['4', '5'])).
% 2.06/2.29  thf('7', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('10', plain,
% 2.06/2.29      (((k1_relat_1 @ sk_A) = (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))),
% 2.06/2.29      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 2.06/2.29  thf('11', plain,
% 2.06/2.29      ((((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B)) | ~ (v1_relat_1 @ sk_B))),
% 2.06/2.29      inference('sup+', [status(thm)], ['1', '10'])).
% 2.06/2.29  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('13', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 2.06/2.29      inference('demod', [status(thm)], ['11', '12'])).
% 2.06/2.29  thf('14', plain,
% 2.06/2.29      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 2.06/2.29      inference('demod', [status(thm)], ['0', '13'])).
% 2.06/2.29  thf(t61_funct_1, axiom,
% 2.06/2.29    (![A:$i]:
% 2.06/2.29     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.06/2.29       ( ( v2_funct_1 @ A ) =>
% 2.06/2.29         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 2.06/2.29             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 2.06/2.29           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 2.06/2.29             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.06/2.29  thf('15', plain,
% 2.06/2.29      (![X19 : $i]:
% 2.06/2.29         (~ (v2_funct_1 @ X19)
% 2.06/2.29          | ((k5_relat_1 @ (k2_funct_1 @ X19) @ X19)
% 2.06/2.29              = (k6_relat_1 @ (k2_relat_1 @ X19)))
% 2.06/2.29          | ~ (v1_funct_1 @ X19)
% 2.06/2.29          | ~ (v1_relat_1 @ X19))),
% 2.06/2.29      inference('cnf', [status(esa)], [t61_funct_1])).
% 2.06/2.29  thf('16', plain,
% 2.06/2.29      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_A)))),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf(dt_k2_funct_1, axiom,
% 2.06/2.29    (![A:$i]:
% 2.06/2.29     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.06/2.29       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.06/2.29         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.06/2.29  thf('17', plain,
% 2.06/2.29      (![X15 : $i]:
% 2.06/2.29         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 2.06/2.29          | ~ (v1_funct_1 @ X15)
% 2.06/2.29          | ~ (v1_relat_1 @ X15))),
% 2.06/2.29      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.06/2.29  thf(t55_funct_1, axiom,
% 2.06/2.29    (![A:$i]:
% 2.06/2.29     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.06/2.29       ( ( v2_funct_1 @ A ) =>
% 2.06/2.29         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.06/2.29           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.06/2.29  thf('18', plain,
% 2.06/2.29      (![X18 : $i]:
% 2.06/2.29         (~ (v2_funct_1 @ X18)
% 2.06/2.29          | ((k1_relat_1 @ X18) = (k2_relat_1 @ (k2_funct_1 @ X18)))
% 2.06/2.29          | ~ (v1_funct_1 @ X18)
% 2.06/2.29          | ~ (v1_relat_1 @ X18))),
% 2.06/2.29      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.06/2.29  thf(t80_relat_1, axiom,
% 2.06/2.29    (![A:$i]:
% 2.06/2.29     ( ( v1_relat_1 @ A ) =>
% 2.06/2.29       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 2.06/2.29  thf('19', plain,
% 2.06/2.29      (![X14 : $i]:
% 2.06/2.29         (((k5_relat_1 @ X14 @ (k6_relat_1 @ (k2_relat_1 @ X14))) = (X14))
% 2.06/2.29          | ~ (v1_relat_1 @ X14))),
% 2.06/2.29      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.06/2.29  thf('20', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.06/2.29            = (k2_funct_1 @ X0))
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_funct_1 @ X0)
% 2.06/2.29          | ~ (v2_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.06/2.29      inference('sup+', [status(thm)], ['18', '19'])).
% 2.06/2.29  thf('21', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_funct_1 @ X0)
% 2.06/2.29          | ~ (v2_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.06/2.29              = (k2_funct_1 @ X0)))),
% 2.06/2.29      inference('sup-', [status(thm)], ['17', '20'])).
% 2.06/2.29  thf('22', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.06/2.29            = (k2_funct_1 @ X0))
% 2.06/2.29          | ~ (v2_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('simplify', [status(thm)], ['21'])).
% 2.06/2.29  thf('23', plain,
% 2.06/2.29      ((((k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B))
% 2.06/2.29          = (k2_funct_1 @ sk_A))
% 2.06/2.29        | ~ (v1_relat_1 @ sk_A)
% 2.06/2.29        | ~ (v1_funct_1 @ sk_A)
% 2.06/2.29        | ~ (v2_funct_1 @ sk_A))),
% 2.06/2.29      inference('sup+', [status(thm)], ['16', '22'])).
% 2.06/2.29  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('25', plain, ((v1_funct_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('26', plain, ((v2_funct_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('27', plain,
% 2.06/2.29      (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ sk_B))
% 2.06/2.29         = (k2_funct_1 @ sk_A))),
% 2.06/2.29      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 2.06/2.29  thf('28', plain,
% 2.06/2.29      (((k5_relat_1 @ sk_A @ sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_B)))),
% 2.06/2.29      inference('demod', [status(thm)], ['0', '13'])).
% 2.06/2.29  thf('29', plain,
% 2.06/2.29      (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 2.06/2.29         = (k2_funct_1 @ sk_A))),
% 2.06/2.29      inference('demod', [status(thm)], ['27', '28'])).
% 2.06/2.29  thf(t55_relat_1, axiom,
% 2.06/2.29    (![A:$i]:
% 2.06/2.29     ( ( v1_relat_1 @ A ) =>
% 2.06/2.29       ( ![B:$i]:
% 2.06/2.29         ( ( v1_relat_1 @ B ) =>
% 2.06/2.29           ( ![C:$i]:
% 2.06/2.29             ( ( v1_relat_1 @ C ) =>
% 2.06/2.29               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 2.06/2.29                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 2.06/2.29  thf('30', plain,
% 2.06/2.29      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X7)
% 2.06/2.29          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 2.06/2.29              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 2.06/2.29          | ~ (v1_relat_1 @ X9)
% 2.06/2.29          | ~ (v1_relat_1 @ X8))),
% 2.06/2.29      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.06/2.29  thf('31', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ X0)
% 2.06/2.29            = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ 
% 2.06/2.29               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ X0)))
% 2.06/2.29          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 2.06/2.29      inference('sup+', [status(thm)], ['29', '30'])).
% 2.06/2.29  thf(fc4_funct_1, axiom,
% 2.06/2.29    (![A:$i]:
% 2.06/2.29     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.06/2.29       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.06/2.29  thf('32', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('33', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ X0)
% 2.06/2.29            = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ 
% 2.06/2.29               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ X0)))
% 2.06/2.29          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('demod', [status(thm)], ['31', '32'])).
% 2.06/2.29  thf('34', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('35', plain,
% 2.06/2.29      (![X15 : $i]:
% 2.06/2.29         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 2.06/2.29          | ~ (v1_funct_1 @ X15)
% 2.06/2.29          | ~ (v1_relat_1 @ X15))),
% 2.06/2.29      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.06/2.29  thf('36', plain,
% 2.06/2.29      (![X18 : $i]:
% 2.06/2.29         (~ (v2_funct_1 @ X18)
% 2.06/2.29          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 2.06/2.29          | ~ (v1_funct_1 @ X18)
% 2.06/2.29          | ~ (v1_relat_1 @ X18))),
% 2.06/2.29      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.06/2.29  thf('37', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 2.06/2.29      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.06/2.29  thf('38', plain,
% 2.06/2.29      (![X14 : $i]:
% 2.06/2.29         (((k5_relat_1 @ X14 @ (k6_relat_1 @ (k2_relat_1 @ X14))) = (X14))
% 2.06/2.29          | ~ (v1_relat_1 @ X14))),
% 2.06/2.29      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.06/2.29  thf('39', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.06/2.29            = (k6_relat_1 @ X0))
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.06/2.29      inference('sup+', [status(thm)], ['37', '38'])).
% 2.06/2.29  thf('40', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('41', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.06/2.29           = (k6_relat_1 @ X0))),
% 2.06/2.29      inference('demod', [status(thm)], ['39', '40'])).
% 2.06/2.29  thf(t44_relat_1, axiom,
% 2.06/2.29    (![A:$i]:
% 2.06/2.29     ( ( v1_relat_1 @ A ) =>
% 2.06/2.29       ( ![B:$i]:
% 2.06/2.29         ( ( v1_relat_1 @ B ) =>
% 2.06/2.29           ( r1_tarski @
% 2.06/2.29             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 2.06/2.29  thf('42', plain,
% 2.06/2.29      (![X5 : $i, X6 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X5)
% 2.06/2.29          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X6 @ X5)) @ 
% 2.06/2.29             (k1_relat_1 @ X6))
% 2.06/2.29          | ~ (v1_relat_1 @ X6))),
% 2.06/2.29      inference('cnf', [status(esa)], [t44_relat_1])).
% 2.06/2.29  thf('43', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         ((r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 2.06/2.29           (k1_relat_1 @ (k6_relat_1 @ X0)))
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.06/2.29      inference('sup+', [status(thm)], ['41', '42'])).
% 2.06/2.29  thf('44', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 2.06/2.29      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.06/2.29  thf('45', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 2.06/2.29      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.06/2.29  thf('46', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('47', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('48', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 2.06/2.29      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 2.06/2.29  thf(t77_relat_1, axiom,
% 2.06/2.29    (![A:$i,B:$i]:
% 2.06/2.29     ( ( v1_relat_1 @ B ) =>
% 2.06/2.29       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 2.06/2.29         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 2.06/2.29  thf('49', plain,
% 2.06/2.29      (![X12 : $i, X13 : $i]:
% 2.06/2.29         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 2.06/2.29          | ((k5_relat_1 @ (k6_relat_1 @ X13) @ X12) = (X12))
% 2.06/2.29          | ~ (v1_relat_1 @ X12))),
% 2.06/2.29      inference('cnf', [status(esa)], [t77_relat_1])).
% 2.06/2.29  thf('50', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X0)
% 2.06/2.29          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 2.06/2.29      inference('sup-', [status(thm)], ['48', '49'])).
% 2.06/2.29  thf('51', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.06/2.29           = (k6_relat_1 @ X0))),
% 2.06/2.29      inference('demod', [status(thm)], ['39', '40'])).
% 2.06/2.29  thf('52', plain,
% 2.06/2.29      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X7)
% 2.06/2.29          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 2.06/2.29              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 2.06/2.29          | ~ (v1_relat_1 @ X9)
% 2.06/2.29          | ~ (v1_relat_1 @ X8))),
% 2.06/2.29      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.06/2.29  thf(dt_k5_relat_1, axiom,
% 2.06/2.29    (![A:$i,B:$i]:
% 2.06/2.29     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 2.06/2.29       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 2.06/2.29  thf('53', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 2.06/2.29      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.06/2.29  thf('54', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.29         ((v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 2.06/2.29          | ~ (v1_relat_1 @ X2)
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 2.06/2.29      inference('sup+', [status(thm)], ['52', '53'])).
% 2.06/2.29  thf('55', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X2)
% 2.06/2.29          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 2.06/2.29      inference('simplify', [status(thm)], ['54'])).
% 2.06/2.29  thf('56', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.06/2.29          | (v1_relat_1 @ 
% 2.06/2.29             (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.06/2.29              (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.06/2.29      inference('sup-', [status(thm)], ['51', '55'])).
% 2.06/2.29  thf('57', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('58', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('59', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('60', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         ((v1_relat_1 @ 
% 2.06/2.29           (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.06/2.29            (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 2.06/2.29          | ~ (v1_relat_1 @ X1))),
% 2.06/2.29      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 2.06/2.29  thf('61', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('sup+', [status(thm)], ['50', '60'])).
% 2.06/2.29  thf('62', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X0)
% 2.06/2.29          | (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0)))),
% 2.06/2.29      inference('simplify', [status(thm)], ['61'])).
% 2.06/2.29  thf('63', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         ((v1_relat_1 @ 
% 2.06/2.29           (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)))
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_funct_1 @ X0)
% 2.06/2.29          | ~ (v2_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.06/2.29      inference('sup+', [status(thm)], ['36', '62'])).
% 2.06/2.29  thf('64', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_funct_1 @ X0)
% 2.06/2.29          | ~ (v2_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | (v1_relat_1 @ 
% 2.06/2.29             (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))))),
% 2.06/2.29      inference('sup-', [status(thm)], ['35', '63'])).
% 2.06/2.29  thf('65', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         ((v1_relat_1 @ 
% 2.06/2.29           (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)))
% 2.06/2.29          | ~ (v2_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('simplify', [status(thm)], ['64'])).
% 2.06/2.29  thf('66', plain,
% 2.06/2.29      (((v1_relat_1 @ 
% 2.06/2.29         (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ (k2_funct_1 @ sk_A)))
% 2.06/2.29        | ~ (v1_relat_1 @ sk_A)
% 2.06/2.29        | ~ (v1_funct_1 @ sk_A)
% 2.06/2.29        | ~ (v2_funct_1 @ sk_A))),
% 2.06/2.29      inference('sup+', [status(thm)], ['34', '65'])).
% 2.06/2.29  thf('67', plain,
% 2.06/2.29      (![X15 : $i]:
% 2.06/2.29         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 2.06/2.29          | ~ (v1_funct_1 @ X15)
% 2.06/2.29          | ~ (v1_relat_1 @ X15))),
% 2.06/2.29      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.06/2.29  thf('68', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('69', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.06/2.29            = (k2_funct_1 @ X0))
% 2.06/2.29          | ~ (v2_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('simplify', [status(thm)], ['21'])).
% 2.06/2.29  thf('70', plain,
% 2.06/2.29      (![X15 : $i]:
% 2.06/2.29         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 2.06/2.29          | ~ (v1_funct_1 @ X15)
% 2.06/2.29          | ~ (v1_relat_1 @ X15))),
% 2.06/2.29      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.06/2.29  thf('71', plain,
% 2.06/2.29      (![X18 : $i]:
% 2.06/2.29         (~ (v2_funct_1 @ X18)
% 2.06/2.29          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 2.06/2.29          | ~ (v1_funct_1 @ X18)
% 2.06/2.29          | ~ (v1_relat_1 @ X18))),
% 2.06/2.29      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.06/2.29  thf('72', plain,
% 2.06/2.29      (![X5 : $i, X6 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X5)
% 2.06/2.29          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X6 @ X5)) @ 
% 2.06/2.29             (k1_relat_1 @ X6))
% 2.06/2.29          | ~ (v1_relat_1 @ X6))),
% 2.06/2.29      inference('cnf', [status(esa)], [t44_relat_1])).
% 2.06/2.29  thf('73', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)) @ 
% 2.06/2.29           (k2_relat_1 @ X0))
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_funct_1 @ X0)
% 2.06/2.29          | ~ (v2_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.06/2.29          | ~ (v1_relat_1 @ X1))),
% 2.06/2.29      inference('sup+', [status(thm)], ['71', '72'])).
% 2.06/2.29  thf('74', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v2_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | (r1_tarski @ 
% 2.06/2.29             (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)) @ 
% 2.06/2.29             (k2_relat_1 @ X0)))),
% 2.06/2.29      inference('sup-', [status(thm)], ['70', '73'])).
% 2.06/2.29  thf('75', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)) @ 
% 2.06/2.29           (k2_relat_1 @ X0))
% 2.06/2.29          | ~ (v2_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v1_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('simplify', [status(thm)], ['74'])).
% 2.06/2.29  thf('76', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_funct_1 @ X0)
% 2.06/2.29          | ~ (v2_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.06/2.29          | ~ (v2_funct_1 @ X0))),
% 2.06/2.29      inference('sup+', [status(thm)], ['69', '75'])).
% 2.06/2.29  thf('77', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('78', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_funct_1 @ X0)
% 2.06/2.29          | ~ (v2_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_funct_1 @ X0)
% 2.06/2.29          | ~ (v2_funct_1 @ X0))),
% 2.06/2.29      inference('demod', [status(thm)], ['76', '77'])).
% 2.06/2.29  thf('79', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (~ (v2_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_funct_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 2.06/2.29      inference('simplify', [status(thm)], ['78'])).
% 2.06/2.29  thf('80', plain,
% 2.06/2.29      (((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_A)) @ (k1_relat_1 @ sk_B))
% 2.06/2.29        | ~ (v1_relat_1 @ sk_A)
% 2.06/2.29        | ~ (v1_funct_1 @ sk_A)
% 2.06/2.29        | ~ (v2_funct_1 @ sk_A))),
% 2.06/2.29      inference('sup+', [status(thm)], ['68', '79'])).
% 2.06/2.29  thf('81', plain, ((v1_relat_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('82', plain, ((v1_funct_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('83', plain, ((v2_funct_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('84', plain,
% 2.06/2.29      ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_A)) @ (k1_relat_1 @ sk_B))),
% 2.06/2.29      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 2.06/2.29  thf('85', plain,
% 2.06/2.29      (![X12 : $i, X13 : $i]:
% 2.06/2.29         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 2.06/2.29          | ((k5_relat_1 @ (k6_relat_1 @ X13) @ X12) = (X12))
% 2.06/2.29          | ~ (v1_relat_1 @ X12))),
% 2.06/2.29      inference('cnf', [status(esa)], [t77_relat_1])).
% 2.06/2.29  thf('86', plain,
% 2.06/2.29      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 2.06/2.29        | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 2.06/2.29            (k2_funct_1 @ sk_A)) = (k2_funct_1 @ sk_A)))),
% 2.06/2.29      inference('sup-', [status(thm)], ['84', '85'])).
% 2.06/2.29  thf('87', plain,
% 2.06/2.29      ((~ (v1_relat_1 @ sk_A)
% 2.06/2.29        | ~ (v1_funct_1 @ sk_A)
% 2.06/2.29        | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 2.06/2.29            (k2_funct_1 @ sk_A)) = (k2_funct_1 @ sk_A)))),
% 2.06/2.29      inference('sup-', [status(thm)], ['67', '86'])).
% 2.06/2.29  thf('88', plain, ((v1_relat_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('89', plain, ((v1_funct_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('90', plain,
% 2.06/2.29      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ (k2_funct_1 @ sk_A))
% 2.06/2.29         = (k2_funct_1 @ sk_A))),
% 2.06/2.29      inference('demod', [status(thm)], ['87', '88', '89'])).
% 2.06/2.29  thf('91', plain, ((v1_relat_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('92', plain, ((v1_funct_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('93', plain, ((v2_funct_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('94', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_A))),
% 2.06/2.29      inference('demod', [status(thm)], ['66', '90', '91', '92', '93'])).
% 2.06/2.29  thf('95', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ X0)
% 2.06/2.29            = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ 
% 2.06/2.29               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ X0)))
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('demod', [status(thm)], ['33', '94'])).
% 2.06/2.29  thf('96', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('97', plain,
% 2.06/2.29      (![X14 : $i]:
% 2.06/2.29         (((k5_relat_1 @ X14 @ (k6_relat_1 @ (k2_relat_1 @ X14))) = (X14))
% 2.06/2.29          | ~ (v1_relat_1 @ X14))),
% 2.06/2.29      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.06/2.29  thf('98', plain,
% 2.06/2.29      ((((k5_relat_1 @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B))) = (sk_A))
% 2.06/2.29        | ~ (v1_relat_1 @ sk_A))),
% 2.06/2.29      inference('sup+', [status(thm)], ['96', '97'])).
% 2.06/2.29  thf('99', plain, ((v1_relat_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('100', plain,
% 2.06/2.29      (((k5_relat_1 @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B))) = (sk_A))),
% 2.06/2.29      inference('demod', [status(thm)], ['98', '99'])).
% 2.06/2.29  thf('101', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.06/2.29           = (k6_relat_1 @ X0))),
% 2.06/2.29      inference('demod', [status(thm)], ['39', '40'])).
% 2.06/2.29  thf('102', plain,
% 2.06/2.29      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X7)
% 2.06/2.29          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 2.06/2.29              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 2.06/2.29          | ~ (v1_relat_1 @ X9)
% 2.06/2.29          | ~ (v1_relat_1 @ X8))),
% 2.06/2.29      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.06/2.29  thf('103', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.06/2.29            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.06/2.29               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.06/2.29      inference('sup+', [status(thm)], ['101', '102'])).
% 2.06/2.29  thf('104', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('105', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('106', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.06/2.29            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.06/2.29               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 2.06/2.29          | ~ (v1_relat_1 @ X1))),
% 2.06/2.29      inference('demod', [status(thm)], ['103', '104', '105'])).
% 2.06/2.29  thf('107', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 2.06/2.29      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.06/2.29  thf('108', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X2)
% 2.06/2.29          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 2.06/2.29      inference('simplify', [status(thm)], ['54'])).
% 2.06/2.29  thf('109', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v1_relat_1 @ X2)
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('sup-', [status(thm)], ['107', '108'])).
% 2.06/2.29  thf('110', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X2)
% 2.06/2.29          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('simplify', [status(thm)], ['109'])).
% 2.06/2.29  thf('111', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('sup+', [status(thm)], ['106', '110'])).
% 2.06/2.29  thf('112', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('113', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('114', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('demod', [status(thm)], ['111', '112', '113'])).
% 2.06/2.29  thf('115', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X0)
% 2.06/2.29          | (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 2.06/2.29      inference('simplify', [status(thm)], ['114'])).
% 2.06/2.29  thf('116', plain,
% 2.06/2.29      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X7)
% 2.06/2.29          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 2.06/2.29              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 2.06/2.29          | ~ (v1_relat_1 @ X9)
% 2.06/2.29          | ~ (v1_relat_1 @ X8))),
% 2.06/2.29      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.06/2.29  thf('117', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.06/2.29           = (k6_relat_1 @ X0))),
% 2.06/2.29      inference('demod', [status(thm)], ['39', '40'])).
% 2.06/2.29  thf('118', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X2)
% 2.06/2.29          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('simplify', [status(thm)], ['109'])).
% 2.06/2.29  thf('119', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         ((v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.06/2.29      inference('sup+', [status(thm)], ['117', '118'])).
% 2.06/2.29  thf('120', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('121', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('122', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         ((v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.06/2.29          | ~ (v1_relat_1 @ X1))),
% 2.06/2.29      inference('demod', [status(thm)], ['119', '120', '121'])).
% 2.06/2.29  thf('123', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.29         ((v1_relat_1 @ 
% 2.06/2.29           (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 2.06/2.29          | ~ (v1_relat_1 @ X2)
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 2.06/2.29      inference('sup+', [status(thm)], ['116', '122'])).
% 2.06/2.29  thf('124', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('125', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.29         ((v1_relat_1 @ 
% 2.06/2.29           (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 2.06/2.29          | ~ (v1_relat_1 @ X2)
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 2.06/2.29      inference('demod', [status(thm)], ['123', '124'])).
% 2.06/2.29  thf('126', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 2.06/2.29          | (v1_relat_1 @ 
% 2.06/2.29             (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 2.06/2.29              (k5_relat_1 @ X0 @ (k6_relat_1 @ X2)))))),
% 2.06/2.29      inference('sup-', [status(thm)], ['115', '125'])).
% 2.06/2.29  thf('127', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('128', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | (v1_relat_1 @ 
% 2.06/2.29             (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 2.06/2.29              (k5_relat_1 @ X0 @ (k6_relat_1 @ X2)))))),
% 2.06/2.29      inference('demod', [status(thm)], ['126', '127'])).
% 2.06/2.29  thf('129', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.29         ((v1_relat_1 @ 
% 2.06/2.29           (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 2.06/2.29            (k5_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('simplify', [status(thm)], ['128'])).
% 2.06/2.29  thf('130', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_A))
% 2.06/2.29          | ~ (v1_relat_1 @ sk_A))),
% 2.06/2.29      inference('sup+', [status(thm)], ['100', '129'])).
% 2.06/2.29  thf('131', plain, ((v1_relat_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('132', plain,
% 2.06/2.29      (![X0 : $i]: (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_A))),
% 2.06/2.29      inference('demod', [status(thm)], ['130', '131'])).
% 2.06/2.29  thf('133', plain,
% 2.06/2.29      (![X3 : $i, X4 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X3)
% 2.06/2.29          | ((k2_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 2.06/2.29              = (k9_relat_1 @ X3 @ (k2_relat_1 @ X4)))
% 2.06/2.29          | ~ (v1_relat_1 @ X4))),
% 2.06/2.29      inference('cnf', [status(esa)], [t160_relat_1])).
% 2.06/2.29  thf('134', plain,
% 2.06/2.29      (![X14 : $i]:
% 2.06/2.29         (((k5_relat_1 @ X14 @ (k6_relat_1 @ (k2_relat_1 @ X14))) = (X14))
% 2.06/2.29          | ~ (v1_relat_1 @ X14))),
% 2.06/2.29      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.06/2.29  thf('135', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         (((k5_relat_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 2.06/2.29            (k6_relat_1 @ (k9_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 2.06/2.29            = (k5_relat_1 @ X0 @ X1))
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 2.06/2.29      inference('sup+', [status(thm)], ['133', '134'])).
% 2.06/2.29  thf('136', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ sk_A)
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.06/2.29          | ((k5_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_A) @ 
% 2.06/2.29              (k6_relat_1 @ 
% 2.06/2.29               (k9_relat_1 @ sk_A @ (k2_relat_1 @ (k6_relat_1 @ X0)))))
% 2.06/2.29              = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_A)))),
% 2.06/2.29      inference('sup-', [status(thm)], ['132', '135'])).
% 2.06/2.29  thf('137', plain, ((v1_relat_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('138', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('139', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 2.06/2.29      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.06/2.29  thf('140', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         ((k5_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_A) @ 
% 2.06/2.29           (k6_relat_1 @ (k9_relat_1 @ sk_A @ X0)))
% 2.06/2.29           = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_A))),
% 2.06/2.29      inference('demod', [status(thm)], ['136', '137', '138', '139'])).
% 2.06/2.29  thf('141', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X2)
% 2.06/2.29          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('simplify', [status(thm)], ['109'])).
% 2.06/2.29  thf('142', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         ((v1_relat_1 @ 
% 2.06/2.29           (k5_relat_1 @ X1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_A)))
% 2.06/2.29          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_A))
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ (k9_relat_1 @ sk_A @ X0))))),
% 2.06/2.29      inference('sup+', [status(thm)], ['140', '141'])).
% 2.06/2.29  thf('143', plain,
% 2.06/2.29      (![X0 : $i]: (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_A))),
% 2.06/2.29      inference('demod', [status(thm)], ['130', '131'])).
% 2.06/2.29  thf('144', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('145', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         ((v1_relat_1 @ 
% 2.06/2.29           (k5_relat_1 @ X1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_A)))
% 2.06/2.29          | ~ (v1_relat_1 @ X1))),
% 2.06/2.29      inference('demod', [status(thm)], ['142', '143', '144'])).
% 2.06/2.29  thf('146', plain,
% 2.06/2.29      (((v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 2.06/2.29        | ~ (v1_relat_1 @ sk_A)
% 2.06/2.29        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 2.06/2.29      inference('sup+', [status(thm)], ['95', '145'])).
% 2.06/2.29  thf('147', plain, ((v1_relat_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('148', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_A))),
% 2.06/2.29      inference('demod', [status(thm)], ['66', '90', '91', '92', '93'])).
% 2.06/2.29  thf('149', plain, ((v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))),
% 2.06/2.29      inference('demod', [status(thm)], ['146', '147', '148'])).
% 2.06/2.29  thf('150', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         (((k5_relat_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 2.06/2.29            (k6_relat_1 @ (k9_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 2.06/2.29            = (k5_relat_1 @ X0 @ X1))
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 2.06/2.29      inference('sup+', [status(thm)], ['133', '134'])).
% 2.06/2.29  thf('151', plain,
% 2.06/2.29      ((~ (v1_relat_1 @ sk_A)
% 2.06/2.29        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 2.06/2.29        | ((k5_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A) @ 
% 2.06/2.29            (k6_relat_1 @ 
% 2.06/2.29             (k9_relat_1 @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_A)))))
% 2.06/2.29            = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A)))),
% 2.06/2.29      inference('sup-', [status(thm)], ['149', '150'])).
% 2.06/2.29  thf('152', plain, ((v1_relat_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('153', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_A))),
% 2.06/2.29      inference('demod', [status(thm)], ['66', '90', '91', '92', '93'])).
% 2.06/2.29  thf('154', plain,
% 2.06/2.29      (![X18 : $i]:
% 2.06/2.29         (~ (v2_funct_1 @ X18)
% 2.06/2.29          | ((k1_relat_1 @ X18) = (k2_relat_1 @ (k2_funct_1 @ X18)))
% 2.06/2.29          | ~ (v1_funct_1 @ X18)
% 2.06/2.29          | ~ (v1_relat_1 @ X18))),
% 2.06/2.29      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.06/2.29  thf('155', plain,
% 2.06/2.29      (![X15 : $i]:
% 2.06/2.29         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 2.06/2.29          | ~ (v1_funct_1 @ X15)
% 2.06/2.29          | ~ (v1_relat_1 @ X15))),
% 2.06/2.29      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.06/2.29  thf('156', plain,
% 2.06/2.29      (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 2.06/2.29         = (k2_funct_1 @ sk_A))),
% 2.06/2.29      inference('demod', [status(thm)], ['27', '28'])).
% 2.06/2.29  thf('157', plain,
% 2.06/2.29      (![X3 : $i, X4 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X3)
% 2.06/2.29          | ((k2_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 2.06/2.29              = (k9_relat_1 @ X3 @ (k2_relat_1 @ X4)))
% 2.06/2.29          | ~ (v1_relat_1 @ X4))),
% 2.06/2.29      inference('cnf', [status(esa)], [t160_relat_1])).
% 2.06/2.29  thf('158', plain,
% 2.06/2.29      ((((k2_relat_1 @ (k2_funct_1 @ sk_A))
% 2.06/2.29          = (k9_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 2.06/2.29             (k2_relat_1 @ (k2_funct_1 @ sk_A))))
% 2.06/2.29        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 2.06/2.29        | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 2.06/2.29      inference('sup+', [status(thm)], ['156', '157'])).
% 2.06/2.29  thf('159', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('160', plain,
% 2.06/2.29      ((((k2_relat_1 @ (k2_funct_1 @ sk_A))
% 2.06/2.29          = (k9_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 2.06/2.29             (k2_relat_1 @ (k2_funct_1 @ sk_A))))
% 2.06/2.29        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 2.06/2.29      inference('demod', [status(thm)], ['158', '159'])).
% 2.06/2.29  thf('161', plain,
% 2.06/2.29      ((~ (v1_relat_1 @ sk_A)
% 2.06/2.29        | ~ (v1_funct_1 @ sk_A)
% 2.06/2.29        | ((k2_relat_1 @ (k2_funct_1 @ sk_A))
% 2.06/2.29            = (k9_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 2.06/2.29               (k2_relat_1 @ (k2_funct_1 @ sk_A)))))),
% 2.06/2.29      inference('sup-', [status(thm)], ['155', '160'])).
% 2.06/2.29  thf('162', plain, ((v1_relat_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('163', plain, ((v1_funct_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('164', plain,
% 2.06/2.29      (((k2_relat_1 @ (k2_funct_1 @ sk_A))
% 2.06/2.29         = (k9_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 2.06/2.29            (k2_relat_1 @ (k2_funct_1 @ sk_A))))),
% 2.06/2.29      inference('demod', [status(thm)], ['161', '162', '163'])).
% 2.06/2.29  thf('165', plain,
% 2.06/2.29      ((((k2_relat_1 @ (k2_funct_1 @ sk_A))
% 2.06/2.29          = (k9_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 2.06/2.29             (k1_relat_1 @ sk_A)))
% 2.06/2.29        | ~ (v1_relat_1 @ sk_A)
% 2.06/2.29        | ~ (v1_funct_1 @ sk_A)
% 2.06/2.29        | ~ (v2_funct_1 @ sk_A))),
% 2.06/2.29      inference('sup+', [status(thm)], ['154', '164'])).
% 2.06/2.29  thf('166', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 2.06/2.29      inference('demod', [status(thm)], ['11', '12'])).
% 2.06/2.29  thf('167', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 2.06/2.29      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.06/2.29  thf('168', plain,
% 2.06/2.29      (![X2 : $i]:
% 2.06/2.29         (((k9_relat_1 @ X2 @ (k1_relat_1 @ X2)) = (k2_relat_1 @ X2))
% 2.06/2.29          | ~ (v1_relat_1 @ X2))),
% 2.06/2.29      inference('cnf', [status(esa)], [t146_relat_1])).
% 2.06/2.29  thf('169', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (((k9_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 2.06/2.29            = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.06/2.29      inference('sup+', [status(thm)], ['167', '168'])).
% 2.06/2.29  thf('170', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 2.06/2.29      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.06/2.29  thf('171', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('172', plain,
% 2.06/2.29      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 2.06/2.29      inference('demod', [status(thm)], ['169', '170', '171'])).
% 2.06/2.29  thf('173', plain, ((v1_relat_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('174', plain, ((v1_funct_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('175', plain, ((v2_funct_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('176', plain,
% 2.06/2.29      (((k2_relat_1 @ (k2_funct_1 @ sk_A)) = (k2_relat_1 @ sk_B))),
% 2.06/2.29      inference('demod', [status(thm)],
% 2.06/2.29                ['165', '166', '172', '173', '174', '175'])).
% 2.06/2.29  thf('177', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 2.06/2.29      inference('demod', [status(thm)], ['11', '12'])).
% 2.06/2.29  thf('178', plain,
% 2.06/2.29      (![X2 : $i]:
% 2.06/2.29         (((k9_relat_1 @ X2 @ (k1_relat_1 @ X2)) = (k2_relat_1 @ X2))
% 2.06/2.29          | ~ (v1_relat_1 @ X2))),
% 2.06/2.29      inference('cnf', [status(esa)], [t146_relat_1])).
% 2.06/2.29  thf('179', plain,
% 2.06/2.29      ((((k9_relat_1 @ sk_A @ (k2_relat_1 @ sk_B)) = (k2_relat_1 @ sk_A))
% 2.06/2.29        | ~ (v1_relat_1 @ sk_A))),
% 2.06/2.29      inference('sup+', [status(thm)], ['177', '178'])).
% 2.06/2.29  thf('180', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('181', plain, ((v1_relat_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('182', plain,
% 2.06/2.29      (((k9_relat_1 @ sk_A @ (k2_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 2.06/2.29      inference('demod', [status(thm)], ['179', '180', '181'])).
% 2.06/2.29  thf('183', plain,
% 2.06/2.29      (((k5_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A) @ 
% 2.06/2.29         (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 2.06/2.29         = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))),
% 2.06/2.29      inference('demod', [status(thm)], ['151', '152', '153', '176', '182'])).
% 2.06/2.29  thf('184', plain,
% 2.06/2.29      ((((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_A)) @ 
% 2.06/2.29          (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 2.06/2.29          = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))
% 2.06/2.29        | ~ (v1_relat_1 @ sk_A)
% 2.06/2.29        | ~ (v1_funct_1 @ sk_A)
% 2.06/2.29        | ~ (v2_funct_1 @ sk_A))),
% 2.06/2.29      inference('sup+', [status(thm)], ['15', '183'])).
% 2.06/2.29  thf('185', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('186', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 2.06/2.29           = (k6_relat_1 @ X0))),
% 2.06/2.29      inference('demod', [status(thm)], ['39', '40'])).
% 2.06/2.29  thf('187', plain, ((v1_relat_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('188', plain, ((v1_funct_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('189', plain, ((v2_funct_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('190', plain,
% 2.06/2.29      (((k6_relat_1 @ (k1_relat_1 @ sk_B))
% 2.06/2.29         = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ sk_A))),
% 2.06/2.29      inference('demod', [status(thm)],
% 2.06/2.29                ['184', '185', '186', '187', '188', '189'])).
% 2.06/2.29  thf('191', plain,
% 2.06/2.29      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X7)
% 2.06/2.29          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 2.06/2.29              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 2.06/2.29          | ~ (v1_relat_1 @ X9)
% 2.06/2.29          | ~ (v1_relat_1 @ X8))),
% 2.06/2.29      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.06/2.29  thf('192', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 2.06/2.29            = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 2.06/2.29          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A))
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ sk_A))),
% 2.06/2.29      inference('sup+', [status(thm)], ['190', '191'])).
% 2.06/2.29  thf('193', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_A))),
% 2.06/2.29      inference('demod', [status(thm)], ['66', '90', '91', '92', '93'])).
% 2.06/2.29  thf('194', plain, ((v1_relat_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('195', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)
% 2.06/2.29            = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k5_relat_1 @ sk_A @ X0)))
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('demod', [status(thm)], ['192', '193', '194'])).
% 2.06/2.29  thf('196', plain,
% 2.06/2.29      ((((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B)
% 2.06/2.29          = (k5_relat_1 @ (k2_funct_1 @ sk_A) @ 
% 2.06/2.29             (k6_relat_1 @ (k2_relat_1 @ sk_B))))
% 2.06/2.29        | ~ (v1_relat_1 @ sk_B))),
% 2.06/2.29      inference('sup+', [status(thm)], ['14', '195'])).
% 2.06/2.29  thf('197', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X0)
% 2.06/2.29          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 2.06/2.29      inference('sup-', [status(thm)], ['48', '49'])).
% 2.06/2.29  thf('198', plain,
% 2.06/2.29      (![X14 : $i]:
% 2.06/2.29         (((k5_relat_1 @ X14 @ (k6_relat_1 @ (k2_relat_1 @ X14))) = (X14))
% 2.06/2.29          | ~ (v1_relat_1 @ X14))),
% 2.06/2.29      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.06/2.29  thf('199', plain,
% 2.06/2.29      (![X19 : $i]:
% 2.06/2.29         (~ (v2_funct_1 @ X19)
% 2.06/2.29          | ((k5_relat_1 @ X19 @ (k2_funct_1 @ X19))
% 2.06/2.29              = (k6_relat_1 @ (k1_relat_1 @ X19)))
% 2.06/2.29          | ~ (v1_funct_1 @ X19)
% 2.06/2.29          | ~ (v1_relat_1 @ X19))),
% 2.06/2.29      inference('cnf', [status(esa)], [t61_funct_1])).
% 2.06/2.29  thf('200', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 2.06/2.29      inference('demod', [status(thm)], ['11', '12'])).
% 2.06/2.29  thf('201', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X0)
% 2.06/2.29          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 2.06/2.29      inference('sup-', [status(thm)], ['48', '49'])).
% 2.06/2.29  thf('202', plain,
% 2.06/2.29      ((((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ sk_A) = (sk_A))
% 2.06/2.29        | ~ (v1_relat_1 @ sk_A))),
% 2.06/2.29      inference('sup+', [status(thm)], ['200', '201'])).
% 2.06/2.29  thf('203', plain, ((v1_relat_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('204', plain,
% 2.06/2.29      (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ sk_A) = (sk_A))),
% 2.06/2.29      inference('demod', [status(thm)], ['202', '203'])).
% 2.06/2.29  thf('205', plain,
% 2.06/2.29      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X7)
% 2.06/2.29          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 2.06/2.29              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 2.06/2.29          | ~ (v1_relat_1 @ X9)
% 2.06/2.29          | ~ (v1_relat_1 @ X8))),
% 2.06/2.29      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.06/2.29  thf('206', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (((k5_relat_1 @ sk_A @ X0)
% 2.06/2.29            = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 2.06/2.29               (k5_relat_1 @ sk_A @ X0)))
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ sk_A))),
% 2.06/2.29      inference('sup+', [status(thm)], ['204', '205'])).
% 2.06/2.29  thf('207', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('208', plain, ((v1_relat_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('209', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (((k5_relat_1 @ sk_A @ X0)
% 2.06/2.29            = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 2.06/2.29               (k5_relat_1 @ sk_A @ X0)))
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('demod', [status(thm)], ['206', '207', '208'])).
% 2.06/2.29  thf('210', plain,
% 2.06/2.29      (![X14 : $i]:
% 2.06/2.29         (((k5_relat_1 @ X14 @ (k6_relat_1 @ (k2_relat_1 @ X14))) = (X14))
% 2.06/2.29          | ~ (v1_relat_1 @ X14))),
% 2.06/2.29      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.06/2.29  thf('211', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X2)
% 2.06/2.29          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 2.06/2.29      inference('simplify', [status(thm)], ['54'])).
% 2.06/2.29  thf('212', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | (v1_relat_1 @ 
% 2.06/2.29             (k5_relat_1 @ X0 @ 
% 2.06/2.29              (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 2.06/2.29      inference('sup-', [status(thm)], ['210', '211'])).
% 2.06/2.29  thf('213', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('214', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | (v1_relat_1 @ 
% 2.06/2.29             (k5_relat_1 @ X0 @ 
% 2.06/2.29              (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X1))),
% 2.06/2.29      inference('demod', [status(thm)], ['212', '213'])).
% 2.06/2.29  thf('215', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X1)
% 2.06/2.29          | (v1_relat_1 @ 
% 2.06/2.29             (k5_relat_1 @ X0 @ 
% 2.06/2.29              (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('simplify', [status(thm)], ['214'])).
% 2.06/2.29  thf('216', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         ((v1_relat_1 @ (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ X0)))
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ sk_B)
% 2.06/2.29          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ X0)))),
% 2.06/2.29      inference('sup+', [status(thm)], ['209', '215'])).
% 2.06/2.29  thf('217', plain, ((v1_relat_1 @ sk_B)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('218', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         ((v1_relat_1 @ (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ X0)))
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ X0)))),
% 2.06/2.29      inference('demod', [status(thm)], ['216', '217'])).
% 2.06/2.29  thf('219', plain,
% 2.06/2.29      (((k5_relat_1 @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B))) = (sk_A))),
% 2.06/2.29      inference('demod', [status(thm)], ['98', '99'])).
% 2.06/2.29  thf('220', plain,
% 2.06/2.29      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X7)
% 2.06/2.29          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 2.06/2.29              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 2.06/2.29          | ~ (v1_relat_1 @ X9)
% 2.06/2.29          | ~ (v1_relat_1 @ X8))),
% 2.06/2.29      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.06/2.29  thf('221', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (((k5_relat_1 @ sk_A @ X0)
% 2.06/2.29            = (k5_relat_1 @ sk_A @ 
% 2.06/2.29               (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)))
% 2.06/2.29          | ~ (v1_relat_1 @ sk_A)
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B))))),
% 2.06/2.29      inference('sup+', [status(thm)], ['219', '220'])).
% 2.06/2.29  thf('222', plain, ((v1_relat_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('223', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('224', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (((k5_relat_1 @ sk_A @ X0)
% 2.06/2.29            = (k5_relat_1 @ sk_A @ 
% 2.06/2.29               (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ X0)))
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('demod', [status(thm)], ['221', '222', '223'])).
% 2.06/2.29  thf('225', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X2)
% 2.06/2.29          | (v1_relat_1 @ (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('simplify', [status(thm)], ['109'])).
% 2.06/2.29  thf('226', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         ((v1_relat_1 @ (k5_relat_1 @ sk_A @ X0))
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 2.06/2.29          | ~ (v1_relat_1 @ sk_A)
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('sup+', [status(thm)], ['224', '225'])).
% 2.06/2.29  thf('227', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('228', plain, ((v1_relat_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('229', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         ((v1_relat_1 @ (k5_relat_1 @ sk_A @ X0))
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('demod', [status(thm)], ['226', '227', '228'])).
% 2.06/2.29  thf('230', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k5_relat_1 @ sk_A @ X0)))),
% 2.06/2.29      inference('simplify', [status(thm)], ['229'])).
% 2.06/2.29  thf('231', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X0)
% 2.06/2.29          | (v1_relat_1 @ (k5_relat_1 @ sk_B @ (k5_relat_1 @ sk_A @ X0))))),
% 2.06/2.29      inference('clc', [status(thm)], ['218', '230'])).
% 2.06/2.29  thf('232', plain,
% 2.06/2.29      (((v1_relat_1 @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k1_relat_1 @ sk_A))))
% 2.06/2.29        | ~ (v1_relat_1 @ sk_A)
% 2.06/2.29        | ~ (v1_funct_1 @ sk_A)
% 2.06/2.29        | ~ (v2_funct_1 @ sk_A)
% 2.06/2.29        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_A)))),
% 2.06/2.29      inference('sup+', [status(thm)], ['199', '231'])).
% 2.06/2.29  thf('233', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 2.06/2.29      inference('demod', [status(thm)], ['11', '12'])).
% 2.06/2.29  thf('234', plain, ((v1_relat_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('235', plain, ((v1_funct_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('236', plain, ((v2_funct_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('237', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_A))),
% 2.06/2.29      inference('demod', [status(thm)], ['66', '90', '91', '92', '93'])).
% 2.06/2.29  thf('238', plain,
% 2.06/2.29      ((v1_relat_1 @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 2.06/2.29      inference('demod', [status(thm)],
% 2.06/2.29                ['232', '233', '234', '235', '236', '237'])).
% 2.06/2.29  thf('239', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         (((k5_relat_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 2.06/2.29            (k6_relat_1 @ (k9_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 2.06/2.29            = (k5_relat_1 @ X0 @ X1))
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 2.06/2.29      inference('sup+', [status(thm)], ['133', '134'])).
% 2.06/2.29  thf('240', plain,
% 2.06/2.29      ((~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 2.06/2.29        | ~ (v1_relat_1 @ sk_B)
% 2.06/2.29        | ((k5_relat_1 @ 
% 2.06/2.29            (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))) @ 
% 2.06/2.29            (k6_relat_1 @ 
% 2.06/2.29             (k9_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 2.06/2.29              (k2_relat_1 @ sk_B))))
% 2.06/2.29            = (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))))),
% 2.06/2.29      inference('sup-', [status(thm)], ['238', '239'])).
% 2.06/2.29  thf('241', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('242', plain, ((v1_relat_1 @ sk_B)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('243', plain,
% 2.06/2.29      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 2.06/2.29      inference('demod', [status(thm)], ['169', '170', '171'])).
% 2.06/2.29  thf('244', plain,
% 2.06/2.29      (((k5_relat_1 @ 
% 2.06/2.29         (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))) @ 
% 2.06/2.29         (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 2.06/2.29         = (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 2.06/2.29      inference('demod', [status(thm)], ['240', '241', '242', '243'])).
% 2.06/2.29  thf('245', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.06/2.29         ((v1_relat_1 @ 
% 2.06/2.29           (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 2.06/2.29            (k5_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 2.06/2.29          | ~ (v1_relat_1 @ X0))),
% 2.06/2.29      inference('simplify', [status(thm)], ['128'])).
% 2.06/2.29  thf('246', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         ((v1_relat_1 @ 
% 2.06/2.29           (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.06/2.29            (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))))
% 2.06/2.29          | ~ (v1_relat_1 @ 
% 2.06/2.29               (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))))),
% 2.06/2.29      inference('sup+', [status(thm)], ['244', '245'])).
% 2.06/2.29  thf('247', plain,
% 2.06/2.29      ((v1_relat_1 @ (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))))),
% 2.06/2.29      inference('demod', [status(thm)],
% 2.06/2.29                ['232', '233', '234', '235', '236', '237'])).
% 2.06/2.29  thf('248', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (v1_relat_1 @ 
% 2.06/2.29          (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.06/2.29           (k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))))),
% 2.06/2.29      inference('demod', [status(thm)], ['246', '247'])).
% 2.06/2.29  thf('249', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))
% 2.06/2.29          | ~ (v1_relat_1 @ sk_B))),
% 2.06/2.29      inference('sup+', [status(thm)], ['198', '248'])).
% 2.06/2.29  thf('250', plain, ((v1_relat_1 @ sk_B)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('251', plain,
% 2.06/2.29      (![X0 : $i]: (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))),
% 2.06/2.29      inference('demod', [status(thm)], ['249', '250'])).
% 2.06/2.29  thf('252', plain,
% 2.06/2.29      (![X0 : $i, X1 : $i]:
% 2.06/2.29         (((k5_relat_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 2.06/2.29            (k6_relat_1 @ (k9_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 2.06/2.29            = (k5_relat_1 @ X0 @ X1))
% 2.06/2.29          | ~ (v1_relat_1 @ X0)
% 2.06/2.29          | ~ (v1_relat_1 @ X1)
% 2.06/2.29          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 2.06/2.29      inference('sup+', [status(thm)], ['133', '134'])).
% 2.06/2.29  thf('253', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ sk_B)
% 2.06/2.29          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.06/2.29          | ((k5_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B) @ 
% 2.06/2.29              (k6_relat_1 @ 
% 2.06/2.29               (k9_relat_1 @ sk_B @ (k2_relat_1 @ (k6_relat_1 @ X0)))))
% 2.06/2.29              = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B)))),
% 2.06/2.29      inference('sup-', [status(thm)], ['251', '252'])).
% 2.06/2.29  thf('254', plain, ((v1_relat_1 @ sk_B)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('255', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.06/2.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.06/2.29  thf('256', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 2.06/2.29      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.06/2.29  thf('257', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         ((k5_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B) @ 
% 2.06/2.29           (k6_relat_1 @ (k9_relat_1 @ sk_B @ X0)))
% 2.06/2.29           = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))),
% 2.06/2.29      inference('demod', [status(thm)], ['253', '254', '255', '256'])).
% 2.06/2.29  thf('258', plain,
% 2.06/2.29      ((((k5_relat_1 @ sk_B @ 
% 2.06/2.29          (k6_relat_1 @ (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))
% 2.06/2.29          = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B))
% 2.06/2.29        | ~ (v1_relat_1 @ sk_B))),
% 2.06/2.29      inference('sup+', [status(thm)], ['197', '257'])).
% 2.06/2.29  thf('259', plain,
% 2.06/2.29      (![X3 : $i, X4 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X3)
% 2.06/2.29          | ((k2_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 2.06/2.29              = (k9_relat_1 @ X3 @ (k2_relat_1 @ X4)))
% 2.06/2.29          | ~ (v1_relat_1 @ X4))),
% 2.06/2.29      inference('cnf', [status(esa)], [t160_relat_1])).
% 2.06/2.29  thf('260', plain,
% 2.06/2.29      (((k2_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) = (k1_relat_1 @ sk_A))),
% 2.06/2.29      inference('sup+', [status(thm)], ['2', '3'])).
% 2.06/2.29  thf('261', plain,
% 2.06/2.29      ((((k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_A)) = (k1_relat_1 @ sk_A))
% 2.06/2.29        | ~ (v1_relat_1 @ sk_A)
% 2.06/2.29        | ~ (v1_relat_1 @ sk_B))),
% 2.06/2.29      inference('sup+', [status(thm)], ['259', '260'])).
% 2.06/2.29  thf('262', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('263', plain, ((v1_relat_1 @ sk_A)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('264', plain, ((v1_relat_1 @ sk_B)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('265', plain,
% 2.06/2.29      (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k1_relat_1 @ sk_A))),
% 2.06/2.29      inference('demod', [status(thm)], ['261', '262', '263', '264'])).
% 2.06/2.29  thf('266', plain, (((k1_relat_1 @ sk_A) = (k2_relat_1 @ sk_B))),
% 2.06/2.29      inference('demod', [status(thm)], ['11', '12'])).
% 2.06/2.29  thf('267', plain,
% 2.06/2.29      (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 2.06/2.29      inference('demod', [status(thm)], ['265', '266'])).
% 2.06/2.29  thf('268', plain, ((v1_relat_1 @ sk_B)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('269', plain,
% 2.06/2.29      (((k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 2.06/2.29         = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B))),
% 2.06/2.29      inference('demod', [status(thm)], ['258', '267', '268'])).
% 2.06/2.29  thf('270', plain,
% 2.06/2.29      (![X0 : $i]:
% 2.06/2.29         (~ (v1_relat_1 @ X0)
% 2.06/2.29          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 2.06/2.29      inference('sup-', [status(thm)], ['48', '49'])).
% 2.06/2.29  thf('271', plain,
% 2.06/2.29      (((k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 2.06/2.29         = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B))),
% 2.06/2.29      inference('demod', [status(thm)], ['258', '267', '268'])).
% 2.06/2.29  thf('272', plain,
% 2.06/2.29      ((((k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))) = (sk_B))
% 2.06/2.29        | ~ (v1_relat_1 @ sk_B))),
% 2.06/2.29      inference('sup+', [status(thm)], ['270', '271'])).
% 2.06/2.29  thf('273', plain, ((v1_relat_1 @ sk_B)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('274', plain,
% 2.06/2.29      (((k5_relat_1 @ sk_B @ (k6_relat_1 @ (k2_relat_1 @ sk_B))) = (sk_B))),
% 2.06/2.29      inference('demod', [status(thm)], ['272', '273'])).
% 2.06/2.29  thf('275', plain,
% 2.06/2.29      (((sk_B) = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B))),
% 2.06/2.29      inference('demod', [status(thm)], ['269', '274'])).
% 2.06/2.29  thf('276', plain,
% 2.06/2.29      (((k5_relat_1 @ (k2_funct_1 @ sk_A) @ (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 2.06/2.29         = (k2_funct_1 @ sk_A))),
% 2.06/2.29      inference('demod', [status(thm)], ['27', '28'])).
% 2.06/2.29  thf('277', plain, ((v1_relat_1 @ sk_B)),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('278', plain, (((sk_B) = (k2_funct_1 @ sk_A))),
% 2.06/2.29      inference('demod', [status(thm)], ['196', '275', '276', '277'])).
% 2.06/2.29  thf('279', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 2.06/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.29  thf('280', plain, ($false),
% 2.06/2.29      inference('simplify_reflect-', [status(thm)], ['278', '279'])).
% 2.06/2.29  
% 2.06/2.29  % SZS output end Refutation
% 2.06/2.29  
% 2.15/2.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

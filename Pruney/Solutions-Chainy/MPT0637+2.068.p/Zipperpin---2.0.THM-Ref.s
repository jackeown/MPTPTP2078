%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kohv9SayMp

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:06 EST 2020

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :  182 (1430 expanded)
%              Number of leaves         :   29 ( 507 expanded)
%              Depth                    :   30
%              Number of atoms          : 1617 (12020 expanded)
%              Number of equality atoms :  104 ( 825 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k7_relat_1 @ X56 @ X55 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X55 ) @ X56 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_funct_1])).

thf('1',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
     != ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('6',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('7',plain,(
    ! [X52: $i] :
      ( ( ( k5_relat_1 @ X52 @ ( k6_relat_1 @ ( k2_relat_1 @ X52 ) ) )
        = X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('8',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k7_relat_1 @ X56 @ X55 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X55 ) @ X56 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('9',plain,(
    ! [X47: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X47 ) )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v1_relat_1 @ X40 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X41 @ X40 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X40 ) @ ( k4_relat_1 @ X41 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X47: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X47 ) )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('16',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k7_relat_1 @ X56 @ X55 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X55 ) @ X56 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k7_relat_1 @ X56 @ X55 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X55 ) @ X56 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X43 @ X42 ) @ X44 )
        = ( k5_relat_1 @ X43 @ ( k5_relat_1 @ X42 @ X44 ) ) )
      | ~ ( v1_relat_1 @ X44 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('33',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X37 @ X36 ) )
        = ( k9_relat_1 @ X36 @ ( k2_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('39',plain,(
    ! [X46: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('40',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('41',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    ! [X46: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('44',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X37 @ X36 ) )
        = ( k9_relat_1 @ X36 @ ( k2_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('45',plain,(
    ! [X46: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('46',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X39 @ X38 ) ) @ ( k2_relat_1 @ X38 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','53'])).

thf('55',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X45: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('58',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X48 ) @ X49 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X49 ) @ X48 )
        = X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X0 )
      = ( k6_relat_1 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['56','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('69',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X45: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('72',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X53 @ X54 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X53 ) @ X54 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('73',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('74',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X53 @ X54 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X53 ) @ X54 ) ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X48 ) @ X49 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X49 ) @ X48 )
        = X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k7_relat_1 @ X56 @ X55 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X55 ) @ X56 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('81',plain,(
    ! [X46: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('82',plain,(
    ! [X52: $i] :
      ( ( ( k5_relat_1 @ X52 @ ( k6_relat_1 @ ( k2_relat_1 @ X52 ) ) )
        = X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k7_relat_1 @ X56 @ X55 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X55 ) @ X56 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('88',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X43 @ X42 ) @ X44 )
        = ( k5_relat_1 @ X43 @ ( k5_relat_1 @ X42 @ X44 ) ) )
      | ~ ( v1_relat_1 @ X44 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('91',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['86','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('95',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v1_relat_1 @ X34 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k7_relat_1 @ X56 @ X55 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X55 ) @ X56 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('100',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v1_relat_1 @ X34 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['98','104'])).

thf('106',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X43 @ X42 ) @ X44 )
        = ( k5_relat_1 @ X43 @ ( k5_relat_1 @ X42 @ X44 ) ) )
      | ~ ( v1_relat_1 @ X44 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('107',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v1_relat_1 @ X34 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','109'])).

thf('111',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','113'])).

thf('115',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('116',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['80','117'])).

thf('119',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','121'])).

thf('123',plain,(
    ! [X47: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X47 ) )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('124',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v1_relat_1 @ X40 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X41 @ X40 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X40 ) @ ( k4_relat_1 @ X41 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['122','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['128','129','130','131'])).

thf('133',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X39 @ X38 ) ) @ ( k2_relat_1 @ X38 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('136',plain,(
    ! [X46: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('138',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['134','135','136','137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 )
      = ( k6_relat_1 @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','42','66','67','141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','42','66','67','141','142'])).

thf('145',plain,(
    ! [X45: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['143','148'])).

thf('150',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','149'])).

thf('151',plain,(
    $false ),
    inference(simplify,[status(thm)],['150'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kohv9SayMp
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:24:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 1.01/1.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.01/1.21  % Solved by: fo/fo7.sh
% 1.01/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.01/1.21  % done 1301 iterations in 0.739s
% 1.01/1.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.01/1.21  % SZS output start Refutation
% 1.01/1.21  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.01/1.21  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.01/1.21  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.01/1.21  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.01/1.21  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.01/1.21  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.01/1.21  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.01/1.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.01/1.21  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.01/1.21  thf(sk_B_type, type, sk_B: $i).
% 1.01/1.21  thf(sk_A_type, type, sk_A: $i).
% 1.01/1.21  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.01/1.21  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.01/1.21  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.01/1.21  thf(t94_relat_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( v1_relat_1 @ B ) =>
% 1.01/1.21       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 1.01/1.21  thf('0', plain,
% 1.01/1.21      (![X55 : $i, X56 : $i]:
% 1.01/1.21         (((k7_relat_1 @ X56 @ X55) = (k5_relat_1 @ (k6_relat_1 @ X55) @ X56))
% 1.01/1.21          | ~ (v1_relat_1 @ X56))),
% 1.01/1.21      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.01/1.21  thf(t43_funct_1, conjecture,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 1.01/1.21       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.01/1.21  thf(zf_stmt_0, negated_conjecture,
% 1.01/1.21    (~( ![A:$i,B:$i]:
% 1.01/1.21        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 1.01/1.21          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 1.01/1.21    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 1.01/1.21  thf('1', plain,
% 1.01/1.21      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 1.01/1.21         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf(t12_setfam_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.01/1.21  thf('2', plain,
% 1.01/1.21      (![X31 : $i, X32 : $i]:
% 1.01/1.21         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 1.01/1.21      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.01/1.21  thf('3', plain,
% 1.01/1.21      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 1.01/1.21         != (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))))),
% 1.01/1.21      inference('demod', [status(thm)], ['1', '2'])).
% 1.01/1.21  thf('4', plain,
% 1.01/1.21      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 1.01/1.21          != (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))))
% 1.01/1.21        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['0', '3'])).
% 1.01/1.21  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 1.01/1.21  thf('5', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('6', plain,
% 1.01/1.21      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 1.01/1.21         != (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))))),
% 1.01/1.21      inference('demod', [status(thm)], ['4', '5'])).
% 1.01/1.21  thf(t80_relat_1, axiom,
% 1.01/1.21    (![A:$i]:
% 1.01/1.21     ( ( v1_relat_1 @ A ) =>
% 1.01/1.21       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.01/1.21  thf('7', plain,
% 1.01/1.21      (![X52 : $i]:
% 1.01/1.21         (((k5_relat_1 @ X52 @ (k6_relat_1 @ (k2_relat_1 @ X52))) = (X52))
% 1.01/1.21          | ~ (v1_relat_1 @ X52))),
% 1.01/1.21      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.01/1.21  thf('8', plain,
% 1.01/1.21      (![X55 : $i, X56 : $i]:
% 1.01/1.21         (((k7_relat_1 @ X56 @ X55) = (k5_relat_1 @ (k6_relat_1 @ X55) @ X56))
% 1.01/1.21          | ~ (v1_relat_1 @ X56))),
% 1.01/1.21      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.01/1.21  thf(t72_relat_1, axiom,
% 1.01/1.21    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 1.01/1.21  thf('9', plain,
% 1.01/1.21      (![X47 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X47)) = (k6_relat_1 @ X47))),
% 1.01/1.21      inference('cnf', [status(esa)], [t72_relat_1])).
% 1.01/1.21  thf(t54_relat_1, axiom,
% 1.01/1.21    (![A:$i]:
% 1.01/1.21     ( ( v1_relat_1 @ A ) =>
% 1.01/1.21       ( ![B:$i]:
% 1.01/1.21         ( ( v1_relat_1 @ B ) =>
% 1.01/1.21           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.01/1.21             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 1.01/1.21  thf('10', plain,
% 1.01/1.21      (![X40 : $i, X41 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ X40)
% 1.01/1.21          | ((k4_relat_1 @ (k5_relat_1 @ X41 @ X40))
% 1.01/1.21              = (k5_relat_1 @ (k4_relat_1 @ X40) @ (k4_relat_1 @ X41)))
% 1.01/1.21          | ~ (v1_relat_1 @ X41))),
% 1.01/1.21      inference('cnf', [status(esa)], [t54_relat_1])).
% 1.01/1.21  thf('11', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.01/1.21            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 1.01/1.21          | ~ (v1_relat_1 @ X1)
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['9', '10'])).
% 1.01/1.21  thf('12', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('13', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.01/1.21            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 1.01/1.21          | ~ (v1_relat_1 @ X1))),
% 1.01/1.21      inference('demod', [status(thm)], ['11', '12'])).
% 1.01/1.21  thf('14', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.01/1.21            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 1.01/1.21               (k4_relat_1 @ (k6_relat_1 @ X0))))
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['8', '13'])).
% 1.01/1.21  thf('15', plain,
% 1.01/1.21      (![X47 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X47)) = (k6_relat_1 @ X47))),
% 1.01/1.21      inference('cnf', [status(esa)], [t72_relat_1])).
% 1.01/1.21  thf('16', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('17', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('18', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.01/1.21           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 1.01/1.21  thf('19', plain,
% 1.01/1.21      (![X55 : $i, X56 : $i]:
% 1.01/1.21         (((k7_relat_1 @ X56 @ X55) = (k5_relat_1 @ (k6_relat_1 @ X55) @ X56))
% 1.01/1.21          | ~ (v1_relat_1 @ X56))),
% 1.01/1.21      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.01/1.21  thf('20', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.01/1.21           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 1.01/1.21  thf('21', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.01/1.21            = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['19', '20'])).
% 1.01/1.21  thf('22', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('23', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.01/1.21           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.01/1.21      inference('demod', [status(thm)], ['21', '22'])).
% 1.01/1.21  thf('24', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.01/1.21           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('demod', [status(thm)], ['18', '23'])).
% 1.01/1.21  thf('25', plain,
% 1.01/1.21      (![X55 : $i, X56 : $i]:
% 1.01/1.21         (((k7_relat_1 @ X56 @ X55) = (k5_relat_1 @ (k6_relat_1 @ X55) @ X56))
% 1.01/1.21          | ~ (v1_relat_1 @ X56))),
% 1.01/1.21      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.01/1.21  thf(t55_relat_1, axiom,
% 1.01/1.21    (![A:$i]:
% 1.01/1.21     ( ( v1_relat_1 @ A ) =>
% 1.01/1.21       ( ![B:$i]:
% 1.01/1.21         ( ( v1_relat_1 @ B ) =>
% 1.01/1.21           ( ![C:$i]:
% 1.01/1.21             ( ( v1_relat_1 @ C ) =>
% 1.01/1.21               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.01/1.21                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.01/1.21  thf('26', plain,
% 1.01/1.21      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ X42)
% 1.01/1.21          | ((k5_relat_1 @ (k5_relat_1 @ X43 @ X42) @ X44)
% 1.01/1.21              = (k5_relat_1 @ X43 @ (k5_relat_1 @ X42 @ X44)))
% 1.01/1.21          | ~ (v1_relat_1 @ X44)
% 1.01/1.21          | ~ (v1_relat_1 @ X43))),
% 1.01/1.21      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.01/1.21  thf('27', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.01/1.21            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 1.01/1.21          | ~ (v1_relat_1 @ X1)
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.01/1.21          | ~ (v1_relat_1 @ X2)
% 1.01/1.21          | ~ (v1_relat_1 @ X1))),
% 1.01/1.21      inference('sup+', [status(thm)], ['25', '26'])).
% 1.01/1.21  thf('28', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('29', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.01/1.21            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 1.01/1.21          | ~ (v1_relat_1 @ X1)
% 1.01/1.21          | ~ (v1_relat_1 @ X2)
% 1.01/1.21          | ~ (v1_relat_1 @ X1))),
% 1.01/1.21      inference('demod', [status(thm)], ['27', '28'])).
% 1.01/1.21  thf('30', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ X2)
% 1.01/1.21          | ~ (v1_relat_1 @ X1)
% 1.01/1.21          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.01/1.21              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 1.01/1.21      inference('simplify', [status(thm)], ['29'])).
% 1.01/1.21  thf('31', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 1.01/1.21            (k6_relat_1 @ X1))
% 1.01/1.21            = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 1.01/1.21               (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['24', '30'])).
% 1.01/1.21  thf('32', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('33', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('34', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 1.01/1.21           (k6_relat_1 @ X1))
% 1.01/1.21           = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 1.01/1.21              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.01/1.21      inference('demod', [status(thm)], ['31', '32', '33'])).
% 1.01/1.21  thf('35', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.01/1.21            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.01/1.21               (k7_relat_1 @ 
% 1.01/1.21                (k6_relat_1 @ 
% 1.01/1.21                 (k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 1.01/1.21                X1)))
% 1.01/1.21          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['7', '34'])).
% 1.01/1.21  thf('36', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.01/1.21           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('demod', [status(thm)], ['18', '23'])).
% 1.01/1.21  thf(t160_relat_1, axiom,
% 1.01/1.21    (![A:$i]:
% 1.01/1.21     ( ( v1_relat_1 @ A ) =>
% 1.01/1.21       ( ![B:$i]:
% 1.01/1.21         ( ( v1_relat_1 @ B ) =>
% 1.01/1.21           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.01/1.21             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.01/1.21  thf('37', plain,
% 1.01/1.21      (![X36 : $i, X37 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ X36)
% 1.01/1.21          | ((k2_relat_1 @ (k5_relat_1 @ X37 @ X36))
% 1.01/1.21              = (k9_relat_1 @ X36 @ (k2_relat_1 @ X37)))
% 1.01/1.21          | ~ (v1_relat_1 @ X37))),
% 1.01/1.21      inference('cnf', [status(esa)], [t160_relat_1])).
% 1.01/1.21  thf('38', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (((k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.01/1.21            = (k9_relat_1 @ (k6_relat_1 @ X1) @ 
% 1.01/1.21               (k2_relat_1 @ (k6_relat_1 @ X0))))
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['36', '37'])).
% 1.01/1.21  thf(t71_relat_1, axiom,
% 1.01/1.21    (![A:$i]:
% 1.01/1.21     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.01/1.21       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.01/1.21  thf('39', plain, (![X46 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X46)) = (X46))),
% 1.01/1.21      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.01/1.21  thf('40', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('41', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('42', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.01/1.21           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.01/1.21      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 1.01/1.21  thf('43', plain, (![X46 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X46)) = (X46))),
% 1.01/1.21      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.01/1.21  thf('44', plain,
% 1.01/1.21      (![X36 : $i, X37 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ X36)
% 1.01/1.21          | ((k2_relat_1 @ (k5_relat_1 @ X37 @ X36))
% 1.01/1.21              = (k9_relat_1 @ X36 @ (k2_relat_1 @ X37)))
% 1.01/1.21          | ~ (v1_relat_1 @ X37))),
% 1.01/1.21      inference('cnf', [status(esa)], [t160_relat_1])).
% 1.01/1.21  thf('45', plain, (![X46 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X46)) = (X46))),
% 1.01/1.21      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.01/1.21  thf(t45_relat_1, axiom,
% 1.01/1.21    (![A:$i]:
% 1.01/1.21     ( ( v1_relat_1 @ A ) =>
% 1.01/1.21       ( ![B:$i]:
% 1.01/1.21         ( ( v1_relat_1 @ B ) =>
% 1.01/1.21           ( r1_tarski @
% 1.01/1.21             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 1.01/1.21  thf('46', plain,
% 1.01/1.21      (![X38 : $i, X39 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ X38)
% 1.01/1.21          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X39 @ X38)) @ 
% 1.01/1.21             (k2_relat_1 @ X38))
% 1.01/1.21          | ~ (v1_relat_1 @ X39))),
% 1.01/1.21      inference('cnf', [status(esa)], [t45_relat_1])).
% 1.01/1.21  thf('47', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 1.01/1.21           X0)
% 1.01/1.21          | ~ (v1_relat_1 @ X1)
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['45', '46'])).
% 1.01/1.21  thf('48', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('49', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 1.01/1.21           X0)
% 1.01/1.21          | ~ (v1_relat_1 @ X1))),
% 1.01/1.21      inference('demod', [status(thm)], ['47', '48'])).
% 1.01/1.21  thf('50', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X1) @ (k2_relat_1 @ X0)) @ 
% 1.01/1.21           X1)
% 1.01/1.21          | ~ (v1_relat_1 @ X0)
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.01/1.21          | ~ (v1_relat_1 @ X0))),
% 1.01/1.21      inference('sup+', [status(thm)], ['44', '49'])).
% 1.01/1.21  thf('51', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('52', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X1) @ (k2_relat_1 @ X0)) @ 
% 1.01/1.21           X1)
% 1.01/1.21          | ~ (v1_relat_1 @ X0)
% 1.01/1.21          | ~ (v1_relat_1 @ X0))),
% 1.01/1.21      inference('demod', [status(thm)], ['50', '51'])).
% 1.01/1.21  thf('53', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ X0)
% 1.01/1.21          | (r1_tarski @ 
% 1.01/1.21             (k9_relat_1 @ (k6_relat_1 @ X1) @ (k2_relat_1 @ X0)) @ X1))),
% 1.01/1.21      inference('simplify', [status(thm)], ['52'])).
% 1.01/1.21  thf('54', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X1)
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['43', '53'])).
% 1.01/1.21  thf('55', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('56', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X1)),
% 1.01/1.21      inference('demod', [status(thm)], ['54', '55'])).
% 1.01/1.21  thf('57', plain, (![X45 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 1.01/1.21      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.01/1.21  thf(t77_relat_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( v1_relat_1 @ B ) =>
% 1.01/1.21       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.01/1.21         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 1.01/1.21  thf('58', plain,
% 1.01/1.21      (![X48 : $i, X49 : $i]:
% 1.01/1.21         (~ (r1_tarski @ (k1_relat_1 @ X48) @ X49)
% 1.01/1.21          | ((k5_relat_1 @ (k6_relat_1 @ X49) @ X48) = (X48))
% 1.01/1.21          | ~ (v1_relat_1 @ X48))),
% 1.01/1.21      inference('cnf', [status(esa)], [t77_relat_1])).
% 1.01/1.21  thf('59', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (~ (r1_tarski @ X0 @ X1)
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.01/1.21          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 1.01/1.21              = (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['57', '58'])).
% 1.01/1.21  thf('60', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('61', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (~ (r1_tarski @ X0 @ X1)
% 1.01/1.21          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 1.01/1.21              = (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('demod', [status(thm)], ['59', '60'])).
% 1.01/1.21  thf('62', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.01/1.21           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 1.01/1.21  thf('63', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (~ (r1_tarski @ X0 @ X1)
% 1.01/1.21          | ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.01/1.21              = (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('demod', [status(thm)], ['61', '62'])).
% 1.01/1.21  thf('64', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.01/1.21           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.01/1.21      inference('demod', [status(thm)], ['21', '22'])).
% 1.01/1.21  thf('65', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (~ (r1_tarski @ X0 @ X1)
% 1.01/1.21          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('demod', [status(thm)], ['63', '64'])).
% 1.01/1.21  thf('66', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k7_relat_1 @ (k6_relat_1 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ 
% 1.01/1.21           X0) = (k6_relat_1 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['56', '65'])).
% 1.01/1.21  thf('67', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.01/1.21           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('demod', [status(thm)], ['18', '23'])).
% 1.01/1.21  thf(t17_xboole_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.01/1.21  thf('68', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 1.01/1.21      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.01/1.21  thf('69', plain,
% 1.01/1.21      (![X31 : $i, X32 : $i]:
% 1.01/1.21         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 1.01/1.21      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.01/1.21  thf('70', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 1.01/1.21      inference('demod', [status(thm)], ['68', '69'])).
% 1.01/1.21  thf('71', plain, (![X45 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 1.01/1.21      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.01/1.21  thf(t90_relat_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( v1_relat_1 @ B ) =>
% 1.01/1.21       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 1.01/1.21         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.01/1.21  thf('72', plain,
% 1.01/1.21      (![X53 : $i, X54 : $i]:
% 1.01/1.21         (((k1_relat_1 @ (k7_relat_1 @ X53 @ X54))
% 1.01/1.21            = (k3_xboole_0 @ (k1_relat_1 @ X53) @ X54))
% 1.01/1.21          | ~ (v1_relat_1 @ X53))),
% 1.01/1.21      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.01/1.21  thf('73', plain,
% 1.01/1.21      (![X31 : $i, X32 : $i]:
% 1.01/1.21         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 1.01/1.21      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.01/1.21  thf('74', plain,
% 1.01/1.21      (![X53 : $i, X54 : $i]:
% 1.01/1.21         (((k1_relat_1 @ (k7_relat_1 @ X53 @ X54))
% 1.01/1.21            = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X53) @ X54)))
% 1.01/1.21          | ~ (v1_relat_1 @ X53))),
% 1.01/1.21      inference('demod', [status(thm)], ['72', '73'])).
% 1.01/1.21  thf('75', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.01/1.21            = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['71', '74'])).
% 1.01/1.21  thf('76', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('77', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.01/1.21           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 1.01/1.21      inference('demod', [status(thm)], ['75', '76'])).
% 1.01/1.21  thf('78', plain,
% 1.01/1.21      (![X48 : $i, X49 : $i]:
% 1.01/1.21         (~ (r1_tarski @ (k1_relat_1 @ X48) @ X49)
% 1.01/1.21          | ((k5_relat_1 @ (k6_relat_1 @ X49) @ X48) = (X48))
% 1.01/1.21          | ~ (v1_relat_1 @ X48))),
% 1.01/1.21      inference('cnf', [status(esa)], [t77_relat_1])).
% 1.01/1.21  thf('79', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         (~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X2)
% 1.01/1.21          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.01/1.21          | ((k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 1.01/1.21              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.01/1.21              = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['77', '78'])).
% 1.01/1.21  thf('80', plain,
% 1.01/1.21      (![X55 : $i, X56 : $i]:
% 1.01/1.21         (((k7_relat_1 @ X56 @ X55) = (k5_relat_1 @ (k6_relat_1 @ X55) @ X56))
% 1.01/1.21          | ~ (v1_relat_1 @ X56))),
% 1.01/1.21      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.01/1.21  thf('81', plain, (![X46 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X46)) = (X46))),
% 1.01/1.21      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.01/1.21  thf('82', plain,
% 1.01/1.21      (![X52 : $i]:
% 1.01/1.21         (((k5_relat_1 @ X52 @ (k6_relat_1 @ (k2_relat_1 @ X52))) = (X52))
% 1.01/1.21          | ~ (v1_relat_1 @ X52))),
% 1.01/1.21      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.01/1.21  thf('83', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.01/1.21            = (k6_relat_1 @ X0))
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['81', '82'])).
% 1.01/1.21  thf('84', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('85', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.01/1.21           = (k6_relat_1 @ X0))),
% 1.01/1.21      inference('demod', [status(thm)], ['83', '84'])).
% 1.01/1.21  thf('86', plain,
% 1.01/1.21      (![X55 : $i, X56 : $i]:
% 1.01/1.21         (((k7_relat_1 @ X56 @ X55) = (k5_relat_1 @ (k6_relat_1 @ X55) @ X56))
% 1.01/1.21          | ~ (v1_relat_1 @ X56))),
% 1.01/1.21      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.01/1.21  thf('87', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.01/1.21           = (k6_relat_1 @ X0))),
% 1.01/1.21      inference('demod', [status(thm)], ['83', '84'])).
% 1.01/1.21  thf('88', plain,
% 1.01/1.21      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ X42)
% 1.01/1.21          | ((k5_relat_1 @ (k5_relat_1 @ X43 @ X42) @ X44)
% 1.01/1.21              = (k5_relat_1 @ X43 @ (k5_relat_1 @ X42 @ X44)))
% 1.01/1.21          | ~ (v1_relat_1 @ X44)
% 1.01/1.21          | ~ (v1_relat_1 @ X43))),
% 1.01/1.21      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.01/1.21  thf('89', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.01/1.21            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.01/1.21               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.01/1.21          | ~ (v1_relat_1 @ X1)
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['87', '88'])).
% 1.01/1.21  thf('90', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('91', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('92', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.01/1.21            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.01/1.21               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 1.01/1.21          | ~ (v1_relat_1 @ X1))),
% 1.01/1.21      inference('demod', [status(thm)], ['89', '90', '91'])).
% 1.01/1.21  thf('93', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.01/1.21            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k7_relat_1 @ X1 @ X0)))
% 1.01/1.21          | ~ (v1_relat_1 @ X1)
% 1.01/1.21          | ~ (v1_relat_1 @ X1))),
% 1.01/1.21      inference('sup+', [status(thm)], ['86', '92'])).
% 1.01/1.21  thf('94', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ X1)
% 1.01/1.21          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.01/1.21              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k7_relat_1 @ X1 @ X0))))),
% 1.01/1.21      inference('simplify', [status(thm)], ['93'])).
% 1.01/1.21  thf(dt_k5_relat_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 1.01/1.21       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 1.01/1.21  thf('95', plain,
% 1.01/1.21      (![X33 : $i, X34 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ X33)
% 1.01/1.21          | ~ (v1_relat_1 @ X34)
% 1.01/1.21          | (v1_relat_1 @ (k5_relat_1 @ X33 @ X34)))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.01/1.21  thf('96', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.01/1.21          | ~ (v1_relat_1 @ X0)
% 1.01/1.21          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['94', '95'])).
% 1.01/1.21  thf('97', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('98', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.01/1.21          | ~ (v1_relat_1 @ X0)
% 1.01/1.21          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 1.01/1.21      inference('demod', [status(thm)], ['96', '97'])).
% 1.01/1.21  thf('99', plain,
% 1.01/1.21      (![X55 : $i, X56 : $i]:
% 1.01/1.21         (((k7_relat_1 @ X56 @ X55) = (k5_relat_1 @ (k6_relat_1 @ X55) @ X56))
% 1.01/1.21          | ~ (v1_relat_1 @ X56))),
% 1.01/1.21      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.01/1.21  thf('100', plain,
% 1.01/1.21      (![X33 : $i, X34 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ X33)
% 1.01/1.21          | ~ (v1_relat_1 @ X34)
% 1.01/1.21          | (v1_relat_1 @ (k5_relat_1 @ X33 @ X34)))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.01/1.21  thf('101', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.01/1.21          | ~ (v1_relat_1 @ X1)
% 1.01/1.21          | ~ (v1_relat_1 @ X1)
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['99', '100'])).
% 1.01/1.21  thf('102', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('103', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.01/1.21          | ~ (v1_relat_1 @ X1)
% 1.01/1.21          | ~ (v1_relat_1 @ X1))),
% 1.01/1.21      inference('demod', [status(thm)], ['101', '102'])).
% 1.01/1.21  thf('104', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.01/1.21      inference('simplify', [status(thm)], ['103'])).
% 1.01/1.21  thf('105', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ X0)
% 1.01/1.21          | (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.01/1.21      inference('clc', [status(thm)], ['98', '104'])).
% 1.01/1.21  thf('106', plain,
% 1.01/1.21      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ X42)
% 1.01/1.21          | ((k5_relat_1 @ (k5_relat_1 @ X43 @ X42) @ X44)
% 1.01/1.21              = (k5_relat_1 @ X43 @ (k5_relat_1 @ X42 @ X44)))
% 1.01/1.21          | ~ (v1_relat_1 @ X44)
% 1.01/1.21          | ~ (v1_relat_1 @ X43))),
% 1.01/1.21      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.01/1.21  thf('107', plain,
% 1.01/1.21      (![X33 : $i, X34 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ X33)
% 1.01/1.21          | ~ (v1_relat_1 @ X34)
% 1.01/1.21          | (v1_relat_1 @ (k5_relat_1 @ X33 @ X34)))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.01/1.21  thf('108', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         ((v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 1.01/1.21          | ~ (v1_relat_1 @ X2)
% 1.01/1.21          | ~ (v1_relat_1 @ X0)
% 1.01/1.21          | ~ (v1_relat_1 @ X1)
% 1.01/1.21          | ~ (v1_relat_1 @ X0)
% 1.01/1.21          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['106', '107'])).
% 1.01/1.21  thf('109', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 1.01/1.21          | ~ (v1_relat_1 @ X1)
% 1.01/1.21          | ~ (v1_relat_1 @ X0)
% 1.01/1.21          | ~ (v1_relat_1 @ X2)
% 1.01/1.21          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 1.01/1.21      inference('simplify', [status(thm)], ['108'])).
% 1.01/1.21  thf('110', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ X0)
% 1.01/1.21          | (v1_relat_1 @ 
% 1.01/1.21             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.01/1.21          | ~ (v1_relat_1 @ X2)
% 1.01/1.21          | ~ (v1_relat_1 @ X0))),
% 1.01/1.21      inference('sup-', [status(thm)], ['105', '109'])).
% 1.01/1.21  thf('111', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('112', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ X0)
% 1.01/1.21          | (v1_relat_1 @ 
% 1.01/1.21             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 1.01/1.21          | ~ (v1_relat_1 @ X2)
% 1.01/1.21          | ~ (v1_relat_1 @ X0))),
% 1.01/1.21      inference('demod', [status(thm)], ['110', '111'])).
% 1.01/1.21  thf('113', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ X2)
% 1.01/1.21          | (v1_relat_1 @ 
% 1.01/1.21             (k5_relat_1 @ (k6_relat_1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 1.01/1.21          | ~ (v1_relat_1 @ X0))),
% 1.01/1.21      inference('simplify', [status(thm)], ['112'])).
% 1.01/1.21  thf('114', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['85', '113'])).
% 1.01/1.21  thf('115', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('116', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('117', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('demod', [status(thm)], ['114', '115', '116'])).
% 1.01/1.21  thf('118', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['80', '117'])).
% 1.01/1.21  thf('119', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('120', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.01/1.21      inference('demod', [status(thm)], ['118', '119'])).
% 1.01/1.21  thf('121', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         (~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X2)
% 1.01/1.21          | ((k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 1.01/1.21              (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.01/1.21              = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.01/1.21      inference('demod', [status(thm)], ['79', '120'])).
% 1.01/1.21  thf('122', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.01/1.21           (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.01/1.21           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 1.01/1.21      inference('sup-', [status(thm)], ['70', '121'])).
% 1.01/1.21  thf('123', plain,
% 1.01/1.21      (![X47 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X47)) = (k6_relat_1 @ X47))),
% 1.01/1.21      inference('cnf', [status(esa)], [t72_relat_1])).
% 1.01/1.21  thf('124', plain,
% 1.01/1.21      (![X40 : $i, X41 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ X40)
% 1.01/1.21          | ((k4_relat_1 @ (k5_relat_1 @ X41 @ X40))
% 1.01/1.21              = (k5_relat_1 @ (k4_relat_1 @ X40) @ (k4_relat_1 @ X41)))
% 1.01/1.21          | ~ (v1_relat_1 @ X41))),
% 1.01/1.21      inference('cnf', [status(esa)], [t54_relat_1])).
% 1.01/1.21  thf('125', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.01/1.21            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.01/1.21          | ~ (v1_relat_1 @ X1))),
% 1.01/1.21      inference('sup+', [status(thm)], ['123', '124'])).
% 1.01/1.21  thf('126', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('127', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.01/1.21            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 1.01/1.21          | ~ (v1_relat_1 @ X1))),
% 1.01/1.21      inference('demod', [status(thm)], ['125', '126'])).
% 1.01/1.21  thf('128', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.01/1.21            = (k5_relat_1 @ 
% 1.01/1.21               (k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 1.01/1.21               (k6_relat_1 @ X1)))
% 1.01/1.21          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['122', '127'])).
% 1.01/1.21  thf('129', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.01/1.21           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.01/1.21      inference('demod', [status(thm)], ['21', '22'])).
% 1.01/1.21  thf('130', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.01/1.21           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.01/1.21      inference('demod', [status(thm)], ['21', '22'])).
% 1.01/1.21  thf('131', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.01/1.21      inference('demod', [status(thm)], ['118', '119'])).
% 1.01/1.21  thf('132', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.01/1.21           = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 1.01/1.21              (k6_relat_1 @ X1)))),
% 1.01/1.21      inference('demod', [status(thm)], ['128', '129', '130', '131'])).
% 1.01/1.21  thf('133', plain,
% 1.01/1.21      (![X38 : $i, X39 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ X38)
% 1.01/1.21          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X39 @ X38)) @ 
% 1.01/1.21             (k2_relat_1 @ X38))
% 1.01/1.21          | ~ (v1_relat_1 @ X39))),
% 1.01/1.21      inference('cnf', [status(esa)], [t45_relat_1])).
% 1.01/1.21  thf('134', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 1.01/1.21           (k2_relat_1 @ (k6_relat_1 @ X0)))
% 1.01/1.21          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.01/1.21          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['132', '133'])).
% 1.01/1.21  thf('135', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.01/1.21           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.01/1.21      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 1.01/1.21  thf('136', plain, (![X46 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X46)) = (X46))),
% 1.01/1.21      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.01/1.21  thf('137', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.01/1.21      inference('demod', [status(thm)], ['118', '119'])).
% 1.01/1.21  thf('138', plain, (![X35 : $i]: (v1_relat_1 @ (k6_relat_1 @ X35))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.01/1.21  thf('139', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)),
% 1.01/1.21      inference('demod', [status(thm)], ['134', '135', '136', '137', '138'])).
% 1.01/1.21  thf('140', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (~ (r1_tarski @ X0 @ X1)
% 1.01/1.21          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 1.01/1.21      inference('demod', [status(thm)], ['63', '64'])).
% 1.01/1.21  thf('141', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k7_relat_1 @ (k6_relat_1 @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 1.01/1.21           X0) = (k6_relat_1 @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['139', '140'])).
% 1.01/1.21  thf('142', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.01/1.21      inference('demod', [status(thm)], ['118', '119'])).
% 1.01/1.21  thf('143', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.01/1.21           = (k6_relat_1 @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.01/1.21      inference('demod', [status(thm)], ['35', '42', '66', '67', '141', '142'])).
% 1.01/1.21  thf('144', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.01/1.21           = (k6_relat_1 @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.01/1.21      inference('demod', [status(thm)], ['35', '42', '66', '67', '141', '142'])).
% 1.01/1.21  thf('145', plain, (![X45 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 1.01/1.21      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.01/1.21  thf('146', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.01/1.21           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.01/1.21      inference('sup+', [status(thm)], ['144', '145'])).
% 1.01/1.21  thf('147', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.01/1.21           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 1.01/1.21      inference('demod', [status(thm)], ['75', '76'])).
% 1.01/1.21  thf('148', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.01/1.21           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['146', '147'])).
% 1.01/1.21  thf('149', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.01/1.21           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.01/1.21      inference('demod', [status(thm)], ['143', '148'])).
% 1.01/1.21  thf('150', plain,
% 1.01/1.21      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 1.01/1.21         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 1.01/1.21      inference('demod', [status(thm)], ['6', '149'])).
% 1.01/1.21  thf('151', plain, ($false), inference('simplify', [status(thm)], ['150'])).
% 1.01/1.21  
% 1.01/1.21  % SZS output end Refutation
% 1.01/1.21  
% 1.01/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

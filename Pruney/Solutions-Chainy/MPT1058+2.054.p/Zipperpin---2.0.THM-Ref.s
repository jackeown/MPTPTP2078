%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1N5h1eIbPq

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:44 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 108 expanded)
%              Number of leaves         :   31 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  637 ( 828 expanded)
%              Number of equality atoms :   42 (  60 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
           => ( ( k10_relat_1 @ A @ C )
              = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X43: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X39: $i] :
      ( ( ( k10_relat_1 @ X39 @ ( k2_relat_1 @ X39 ) )
        = ( k1_relat_1 @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X42: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('7',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X49 @ ( k10_relat_1 @ X49 @ X50 ) ) @ X50 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,(
    ! [X45: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ),
    inference('sup-',[status(thm)],['0','15'])).

thf('17',plain,(
    ! [X42: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('20',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( r1_tarski @ X51 @ ( k1_relat_1 @ X52 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X52 @ X51 ) @ X53 )
      | ( r1_tarski @ X51 @ ( k10_relat_1 @ X52 @ X53 ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X42: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('24',plain,(
    ! [X45: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf('28',plain,(
    ! [X42: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('29',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X37 @ X38 ) @ ( k1_relat_1 @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( X0
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X55 ) @ ( k6_relat_1 @ X54 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X54 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('38',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X55 ) @ ( k6_relat_1 @ X54 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X54 @ X55 ) ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X42: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('40',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v1_relat_1 @ X40 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X41 @ X40 ) )
        = ( k10_relat_1 @ X41 @ ( k1_relat_1 @ X40 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X42: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('46',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['35','47'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('49',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X47 @ X46 ) @ X48 )
        = ( k3_xboole_0 @ X46 @ ( k10_relat_1 @ X47 @ X48 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('50',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('51',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X47 @ X46 ) @ X48 )
        = ( k1_setfam_1 @ ( k2_tarski @ X46 @ ( k10_relat_1 @ X47 @ X48 ) ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
     != ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1N5h1eIbPq
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.79  % Solved by: fo/fo7.sh
% 0.59/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.79  % done 644 iterations in 0.341s
% 0.59/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.79  % SZS output start Refutation
% 0.59/0.79  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.79  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.59/0.79  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.59/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.79  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.59/0.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.79  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.59/0.79  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.59/0.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.79  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.59/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.79  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.79  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.79  thf(t175_funct_2, conjecture,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.79       ( ![B:$i,C:$i]:
% 0.59/0.79         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.59/0.79           ( ( k10_relat_1 @ A @ C ) =
% 0.59/0.79             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.59/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.79    (~( ![A:$i]:
% 0.59/0.79        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.79          ( ![B:$i,C:$i]:
% 0.59/0.79            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.59/0.79              ( ( k10_relat_1 @ A @ C ) =
% 0.59/0.79                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.59/0.79    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.59/0.79  thf('0', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(t71_relat_1, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.59/0.79       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.59/0.79  thf('1', plain, (![X43 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 0.59/0.79      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.59/0.79  thf(t169_relat_1, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( v1_relat_1 @ A ) =>
% 0.59/0.79       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.59/0.79  thf('2', plain,
% 0.59/0.79      (![X39 : $i]:
% 0.59/0.79         (((k10_relat_1 @ X39 @ (k2_relat_1 @ X39)) = (k1_relat_1 @ X39))
% 0.59/0.79          | ~ (v1_relat_1 @ X39))),
% 0.59/0.79      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.59/0.79  thf('3', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.59/0.79            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.59/0.79          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['1', '2'])).
% 0.59/0.79  thf('4', plain, (![X42 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X42)) = (X42))),
% 0.59/0.79      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.59/0.79  thf(fc3_funct_1, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.59/0.79       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.59/0.79  thf('5', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.59/0.79      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.59/0.79  thf('6', plain,
% 0.59/0.79      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.59/0.79      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.59/0.79  thf(t145_funct_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.79       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.59/0.79  thf('7', plain,
% 0.59/0.79      (![X49 : $i, X50 : $i]:
% 0.59/0.79         ((r1_tarski @ (k9_relat_1 @ X49 @ (k10_relat_1 @ X49 @ X50)) @ X50)
% 0.59/0.79          | ~ (v1_funct_1 @ X49)
% 0.59/0.79          | ~ (v1_relat_1 @ X49))),
% 0.59/0.79      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.59/0.79  thf('8', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X0)
% 0.59/0.79          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.59/0.79          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['6', '7'])).
% 0.59/0.79  thf('9', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.59/0.79      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.59/0.79  thf('10', plain, (![X45 : $i]: (v1_funct_1 @ (k6_relat_1 @ X45))),
% 0.59/0.79      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.59/0.79  thf('11', plain,
% 0.59/0.79      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X0)),
% 0.59/0.79      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.59/0.79  thf(t12_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.59/0.79  thf('12', plain,
% 0.59/0.79      (![X6 : $i, X7 : $i]:
% 0.59/0.79         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.59/0.79      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.59/0.79  thf('13', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((k2_xboole_0 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X0) = (X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.79  thf(t11_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.59/0.79  thf('14', plain,
% 0.59/0.79      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.79         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.59/0.79      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.59/0.79  thf('15', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (r1_tarski @ X0 @ X1)
% 0.59/0.79          | (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['13', '14'])).
% 0.59/0.79  thf('16', plain,
% 0.59/0.79      ((r1_tarski @ 
% 0.59/0.79        (k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.59/0.79         (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.59/0.79        sk_B)),
% 0.59/0.79      inference('sup-', [status(thm)], ['0', '15'])).
% 0.59/0.79  thf('17', plain, (![X42 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X42)) = (X42))),
% 0.59/0.79      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.59/0.79  thf(d10_xboole_0, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.79  thf('18', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.59/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.79  thf('19', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.59/0.79      inference('simplify', [status(thm)], ['18'])).
% 0.59/0.79  thf(t163_funct_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.59/0.79       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.59/0.79           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.59/0.79         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.59/0.79  thf('20', plain,
% 0.59/0.79      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.59/0.79         (~ (r1_tarski @ X51 @ (k1_relat_1 @ X52))
% 0.59/0.79          | ~ (r1_tarski @ (k9_relat_1 @ X52 @ X51) @ X53)
% 0.59/0.79          | (r1_tarski @ X51 @ (k10_relat_1 @ X52 @ X53))
% 0.59/0.79          | ~ (v1_funct_1 @ X52)
% 0.59/0.79          | ~ (v1_relat_1 @ X52))),
% 0.59/0.79      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.59/0.79  thf('21', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X0)
% 0.59/0.79          | ~ (v1_funct_1 @ X0)
% 0.59/0.79          | (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.59/0.79          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.79  thf('22', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.59/0.79          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.59/0.79             (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.59/0.79          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.59/0.79          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['17', '21'])).
% 0.59/0.79  thf('23', plain, (![X42 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X42)) = (X42))),
% 0.59/0.79      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.59/0.79  thf('24', plain, (![X45 : $i]: (v1_funct_1 @ (k6_relat_1 @ X45))),
% 0.59/0.79      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.59/0.79  thf('25', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.59/0.79      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.59/0.79  thf('26', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.59/0.79          | (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.59/0.79      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 0.59/0.79  thf('27', plain,
% 0.59/0.79      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.59/0.79        (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B))),
% 0.59/0.79      inference('sup-', [status(thm)], ['16', '26'])).
% 0.59/0.79  thf('28', plain, (![X42 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X42)) = (X42))),
% 0.59/0.79      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.59/0.79  thf(t167_relat_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( v1_relat_1 @ B ) =>
% 0.59/0.79       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.59/0.79  thf('29', plain,
% 0.59/0.79      (![X37 : $i, X38 : $i]:
% 0.59/0.79         ((r1_tarski @ (k10_relat_1 @ X37 @ X38) @ (k1_relat_1 @ X37))
% 0.59/0.79          | ~ (v1_relat_1 @ X37))),
% 0.59/0.79      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.59/0.79  thf('30', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.59/0.79          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['28', '29'])).
% 0.59/0.79  thf('31', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.59/0.79      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.59/0.79  thf('32', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 0.59/0.79      inference('demod', [status(thm)], ['30', '31'])).
% 0.59/0.79  thf('33', plain,
% 0.59/0.79      (![X0 : $i, X2 : $i]:
% 0.59/0.79         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.59/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.79  thf('34', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.59/0.79          | ((X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['32', '33'])).
% 0.59/0.79  thf('35', plain,
% 0.59/0.79      (((k10_relat_1 @ sk_A @ sk_C)
% 0.59/0.79         = (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B))),
% 0.59/0.79      inference('sup-', [status(thm)], ['27', '34'])).
% 0.59/0.79  thf(t43_funct_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.59/0.79       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.79  thf('36', plain,
% 0.59/0.79      (![X54 : $i, X55 : $i]:
% 0.59/0.79         ((k5_relat_1 @ (k6_relat_1 @ X55) @ (k6_relat_1 @ X54))
% 0.59/0.79           = (k6_relat_1 @ (k3_xboole_0 @ X54 @ X55)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.59/0.79  thf(t12_setfam_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.79  thf('37', plain,
% 0.59/0.79      (![X35 : $i, X36 : $i]:
% 0.59/0.79         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.59/0.79      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.59/0.79  thf('38', plain,
% 0.59/0.79      (![X54 : $i, X55 : $i]:
% 0.59/0.79         ((k5_relat_1 @ (k6_relat_1 @ X55) @ (k6_relat_1 @ X54))
% 0.59/0.79           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X54 @ X55))))),
% 0.59/0.79      inference('demod', [status(thm)], ['36', '37'])).
% 0.59/0.79  thf('39', plain, (![X42 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X42)) = (X42))),
% 0.59/0.79      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.59/0.79  thf(t182_relat_1, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( v1_relat_1 @ A ) =>
% 0.59/0.79       ( ![B:$i]:
% 0.59/0.79         ( ( v1_relat_1 @ B ) =>
% 0.59/0.79           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.59/0.79             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.59/0.79  thf('40', plain,
% 0.59/0.79      (![X40 : $i, X41 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X40)
% 0.59/0.79          | ((k1_relat_1 @ (k5_relat_1 @ X41 @ X40))
% 0.59/0.79              = (k10_relat_1 @ X41 @ (k1_relat_1 @ X40)))
% 0.59/0.79          | ~ (v1_relat_1 @ X41))),
% 0.59/0.79      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.59/0.79  thf('41', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.59/0.79            = (k10_relat_1 @ X1 @ X0))
% 0.59/0.79          | ~ (v1_relat_1 @ X1)
% 0.59/0.79          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['39', '40'])).
% 0.59/0.79  thf('42', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.59/0.79      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.59/0.79  thf('43', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.59/0.79            = (k10_relat_1 @ X1 @ X0))
% 0.59/0.79          | ~ (v1_relat_1 @ X1))),
% 0.59/0.79      inference('demod', [status(thm)], ['41', '42'])).
% 0.59/0.79  thf('44', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (((k1_relat_1 @ (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.59/0.79            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.59/0.79          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['38', '43'])).
% 0.59/0.79  thf('45', plain, (![X42 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X42)) = (X42))),
% 0.59/0.79      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.59/0.79  thf('46', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.59/0.79      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.59/0.79  thf('47', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.59/0.79           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.59/0.79      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.59/0.79  thf('48', plain,
% 0.59/0.79      (((k10_relat_1 @ sk_A @ sk_C)
% 0.59/0.79         = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.59/0.79      inference('demod', [status(thm)], ['35', '47'])).
% 0.59/0.79  thf(t139_funct_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( v1_relat_1 @ C ) =>
% 0.59/0.79       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.59/0.79         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.59/0.79  thf('49', plain,
% 0.59/0.79      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.59/0.79         (((k10_relat_1 @ (k7_relat_1 @ X47 @ X46) @ X48)
% 0.59/0.79            = (k3_xboole_0 @ X46 @ (k10_relat_1 @ X47 @ X48)))
% 0.59/0.79          | ~ (v1_relat_1 @ X47))),
% 0.59/0.79      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.59/0.79  thf('50', plain,
% 0.59/0.79      (![X35 : $i, X36 : $i]:
% 0.59/0.79         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.59/0.79      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.59/0.79  thf('51', plain,
% 0.59/0.79      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.59/0.79         (((k10_relat_1 @ (k7_relat_1 @ X47 @ X46) @ X48)
% 0.59/0.79            = (k1_setfam_1 @ (k2_tarski @ X46 @ (k10_relat_1 @ X47 @ X48))))
% 0.59/0.79          | ~ (v1_relat_1 @ X47))),
% 0.59/0.79      inference('demod', [status(thm)], ['49', '50'])).
% 0.59/0.79  thf('52', plain,
% 0.59/0.79      (((k10_relat_1 @ sk_A @ sk_C)
% 0.59/0.79         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('53', plain,
% 0.59/0.79      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.59/0.79          != (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))
% 0.59/0.79        | ~ (v1_relat_1 @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['51', '52'])).
% 0.59/0.79  thf('54', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('55', plain,
% 0.59/0.79      (((k10_relat_1 @ sk_A @ sk_C)
% 0.59/0.79         != (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.59/0.79      inference('demod', [status(thm)], ['53', '54'])).
% 0.59/0.79  thf('56', plain, ($false),
% 0.59/0.79      inference('simplify_reflect-', [status(thm)], ['48', '55'])).
% 0.59/0.79  
% 0.59/0.79  % SZS output end Refutation
% 0.59/0.79  
% 0.59/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

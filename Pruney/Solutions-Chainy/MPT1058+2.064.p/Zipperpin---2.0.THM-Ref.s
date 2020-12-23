%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wwKVcBioEw

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 279 expanded)
%              Number of leaves         :   29 ( 110 expanded)
%              Depth                    :   13
%              Number of atoms          :  807 (2315 expanded)
%              Number of equality atoms :   59 ( 208 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X41: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X41 ) )
      = X41 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('4',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( r1_tarski @ X54 @ ( k1_relat_1 @ X55 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X55 @ X54 ) @ X56 )
      | ( r1_tarski @ X54 @ ( k10_relat_1 @ X55 @ X56 ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X41: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X41 ) )
      = X41 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X46: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('9',plain,(
    ! [X45: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('12',plain,(
    ! [X42: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('13',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( r1_tarski @ X50 @ ( k2_relat_1 @ X51 ) )
      | ( ( k9_relat_1 @ X51 @ ( k10_relat_1 @ X51 @ X50 ) )
        = X50 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X45: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('16',plain,(
    ! [X46: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X42: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X37: $i] :
      ( ( ( k10_relat_1 @ X37 @ ( k2_relat_1 @ X37 ) )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X41: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X41 ) )
      = X41 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('23',plain,(
    ! [X45: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['18','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['10','25'])).

thf('27',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','26'])).

thf('28',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
    | ( ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B )
      = ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('30',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X48 @ X47 ) @ X49 )
        = ( k3_xboole_0 @ X47 @ ( k10_relat_1 @ X48 @ X49 ) ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('32',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X48 @ X47 ) @ X49 )
        = ( k1_setfam_1 @ ( k2_tarski @ X47 @ ( k10_relat_1 @ X48 @ X49 ) ) ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('33',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k7_relat_1 @ X44 @ X43 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X43 ) @ X44 ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X39 @ X38 ) @ X40 )
        = ( k10_relat_1 @ X39 @ ( k10_relat_1 @ X38 @ X40 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X45: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X1 )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X45: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('41',plain,(
    ! [X45: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('45',plain,(
    ! [X45: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('47',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('48',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('49',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) @ X3 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('51',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['29','46','49','50'])).

thf('52',plain,(
    ! [X41: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X41 ) )
      = X41 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('53',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k9_relat_1 @ X53 @ ( k10_relat_1 @ X53 @ X52 ) )
        = ( k3_xboole_0 @ X52 @ ( k9_relat_1 @ X53 @ ( k1_relat_1 @ X53 ) ) ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('54',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('55',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k9_relat_1 @ X53 @ ( k10_relat_1 @ X53 @ X52 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X52 @ ( k9_relat_1 @ X53 @ ( k1_relat_1 @ X53 ) ) ) ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['18','24'])).

thf('59',plain,(
    ! [X45: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('60',plain,(
    ! [X46: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57','58','59','60'])).

thf('62',plain,
    ( ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['51','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['18','24'])).

thf('64',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X48 @ X47 ) @ X49 )
        = ( k1_setfam_1 @ ( k2_tarski @ X47 @ ( k10_relat_1 @ X48 @ X49 ) ) ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('66',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
     != ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['64','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wwKVcBioEw
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:59:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 124 iterations in 0.062s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(t175_funct_2, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.52       ( ![B:$i,C:$i]:
% 0.20/0.52         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.20/0.52           ( ( k10_relat_1 @ A @ C ) =
% 0.20/0.52             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.52          ( ![B:$i,C:$i]:
% 0.20/0.52            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.20/0.52              ( ( k10_relat_1 @ A @ C ) =
% 0.20/0.52                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.20/0.52  thf('0', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t71_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.52       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.52  thf('1', plain, (![X41 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X41)) = (X41))),
% 0.20/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.52  thf(d10_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.52      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.52  thf(t163_funct_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.52       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.52           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.20/0.52         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.20/0.52         (~ (r1_tarski @ X54 @ (k1_relat_1 @ X55))
% 0.20/0.52          | ~ (r1_tarski @ (k9_relat_1 @ X55 @ X54) @ X56)
% 0.20/0.52          | (r1_tarski @ X54 @ (k10_relat_1 @ X55 @ X56))
% 0.20/0.52          | ~ (v1_funct_1 @ X55)
% 0.20/0.52          | ~ (v1_relat_1 @ X55))),
% 0.20/0.52      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X0)
% 0.20/0.52          | ~ (v1_funct_1 @ X0)
% 0.20/0.52          | (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.20/0.52          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.20/0.52          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.20/0.52             (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.20/0.52          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.20/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '5'])).
% 0.20/0.52  thf('7', plain, (![X41 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X41)) = (X41))),
% 0.20/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.52  thf(fc3_funct_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.52       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.52  thf('8', plain, (![X46 : $i]: (v1_funct_1 @ (k6_relat_1 @ X46))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.52  thf('9', plain, (![X45 : $i]: (v1_relat_1 @ (k6_relat_1 @ X45))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.20/0.52          | (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.20/0.52      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.20/0.52  thf('11', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.52      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.52  thf('12', plain, (![X42 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X42)) = (X42))),
% 0.20/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.52  thf(t147_funct_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.52       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.20/0.52         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X50 : $i, X51 : $i]:
% 0.20/0.52         (~ (r1_tarski @ X50 @ (k2_relat_1 @ X51))
% 0.20/0.52          | ((k9_relat_1 @ X51 @ (k10_relat_1 @ X51 @ X50)) = (X50))
% 0.20/0.52          | ~ (v1_funct_1 @ X51)
% 0.20/0.52          | ~ (v1_relat_1 @ X51))),
% 0.20/0.52      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r1_tarski @ X1 @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.52          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.20/0.52          | ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.20/0.52              (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf('15', plain, (![X45 : $i]: (v1_relat_1 @ (k6_relat_1 @ X45))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.52  thf('16', plain, (![X46 : $i]: (v1_funct_1 @ (k6_relat_1 @ X46))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r1_tarski @ X1 @ X0)
% 0.20/0.52          | ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.20/0.52              (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X1)))),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.20/0.52           (k10_relat_1 @ (k6_relat_1 @ X0) @ X0)) = (X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '17'])).
% 0.20/0.52  thf('19', plain, (![X42 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X42)) = (X42))),
% 0.20/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.52  thf(t169_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X37 : $i]:
% 0.20/0.52         (((k10_relat_1 @ X37 @ (k2_relat_1 @ X37)) = (k1_relat_1 @ X37))
% 0.20/0.52          | ~ (v1_relat_1 @ X37))),
% 0.20/0.52      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.20/0.52            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('22', plain, (![X41 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X41)) = (X41))),
% 0.20/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.52  thf('23', plain, (![X45 : $i]: (v1_relat_1 @ (k6_relat_1 @ X45))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['18', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.52          | (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.20/0.52      inference('demod', [status(thm)], ['10', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.20/0.52        (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '26'])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X0 : $i, X2 : $i]:
% 0.20/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      ((~ (r1_tarski @ 
% 0.20/0.52           (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B) @ 
% 0.20/0.52           (k10_relat_1 @ sk_A @ sk_C))
% 0.20/0.52        | ((k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B)
% 0.20/0.52            = (k10_relat_1 @ sk_A @ sk_C)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf(t139_funct_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ C ) =>
% 0.20/0.52       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.20/0.52         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.20/0.52         (((k10_relat_1 @ (k7_relat_1 @ X48 @ X47) @ X49)
% 0.20/0.52            = (k3_xboole_0 @ X47 @ (k10_relat_1 @ X48 @ X49)))
% 0.20/0.52          | ~ (v1_relat_1 @ X48))),
% 0.20/0.52      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.20/0.52  thf(t12_setfam_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X35 : $i, X36 : $i]:
% 0.20/0.52         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.20/0.52         (((k10_relat_1 @ (k7_relat_1 @ X48 @ X47) @ X49)
% 0.20/0.52            = (k1_setfam_1 @ (k2_tarski @ X47 @ (k10_relat_1 @ X48 @ X49))))
% 0.20/0.52          | ~ (v1_relat_1 @ X48))),
% 0.20/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf(t94_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ B ) =>
% 0.20/0.52       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X43 : $i, X44 : $i]:
% 0.20/0.52         (((k7_relat_1 @ X44 @ X43) = (k5_relat_1 @ (k6_relat_1 @ X43) @ X44))
% 0.20/0.52          | ~ (v1_relat_1 @ X44))),
% 0.20/0.52      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.20/0.52  thf(t181_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ B ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( v1_relat_1 @ C ) =>
% 0.20/0.52           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.20/0.52             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X38)
% 0.20/0.52          | ((k10_relat_1 @ (k5_relat_1 @ X39 @ X38) @ X40)
% 0.20/0.52              = (k10_relat_1 @ X39 @ (k10_relat_1 @ X38 @ X40)))
% 0.20/0.52          | ~ (v1_relat_1 @ X39))),
% 0.20/0.52      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k10_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X0)
% 0.20/0.52            = (k10_relat_1 @ X1 @ X0))
% 0.20/0.52          | ~ (v1_relat_1 @ X1)
% 0.20/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('37', plain, (![X45 : $i]: (v1_relat_1 @ (k6_relat_1 @ X45))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k10_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X0)
% 0.20/0.52            = (k10_relat_1 @ X1 @ X0))
% 0.20/0.52          | ~ (v1_relat_1 @ X1))),
% 0.20/0.52      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X1)
% 0.20/0.52            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.20/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.20/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['33', '38'])).
% 0.20/0.52  thf('40', plain, (![X45 : $i]: (v1_relat_1 @ (k6_relat_1 @ X45))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.52  thf('41', plain, (![X45 : $i]: (v1_relat_1 @ (k6_relat_1 @ X45))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X1)
% 0.20/0.52           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.20/0.52      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k1_setfam_1 @ 
% 0.20/0.52            (k2_tarski @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X0)))
% 0.20/0.52            = (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.20/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['32', '42'])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.20/0.52  thf('45', plain, (![X45 : $i]: (v1_relat_1 @ (k6_relat_1 @ X45))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.20/0.52           = (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.52  thf(t17_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.20/0.52      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X35 : $i, X36 : $i]:
% 0.20/0.52         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]:
% 0.20/0.52         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4)) @ X3)),
% 0.20/0.52      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.20/0.52           = (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (((k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.20/0.52         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.20/0.52      inference('demod', [status(thm)], ['29', '46', '49', '50'])).
% 0.20/0.52  thf('52', plain, (![X41 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X41)) = (X41))),
% 0.20/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.52  thf(t148_funct_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.52       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.20/0.52         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (![X52 : $i, X53 : $i]:
% 0.20/0.52         (((k9_relat_1 @ X53 @ (k10_relat_1 @ X53 @ X52))
% 0.20/0.52            = (k3_xboole_0 @ X52 @ (k9_relat_1 @ X53 @ (k1_relat_1 @ X53))))
% 0.20/0.52          | ~ (v1_funct_1 @ X53)
% 0.20/0.52          | ~ (v1_relat_1 @ X53))),
% 0.20/0.52      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (![X35 : $i, X36 : $i]:
% 0.20/0.52         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      (![X52 : $i, X53 : $i]:
% 0.20/0.52         (((k9_relat_1 @ X53 @ (k10_relat_1 @ X53 @ X52))
% 0.20/0.52            = (k1_setfam_1 @ 
% 0.20/0.52               (k2_tarski @ X52 @ (k9_relat_1 @ X53 @ (k1_relat_1 @ X53)))))
% 0.20/0.52          | ~ (v1_funct_1 @ X53)
% 0.20/0.52          | ~ (v1_relat_1 @ X53))),
% 0.20/0.52      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.20/0.52            (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.20/0.52            = (k1_setfam_1 @ 
% 0.20/0.52               (k2_tarski @ X1 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))))
% 0.20/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.52          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['52', '55'])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.20/0.52           = (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['18', '24'])).
% 0.20/0.52  thf('59', plain, (![X45 : $i]: (v1_relat_1 @ (k6_relat_1 @ X45))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.52  thf('60', plain, (![X46 : $i]: (v1_funct_1 @ (k6_relat_1 @ X46))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.20/0.52           (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 0.20/0.52           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['56', '57', '58', '59', '60'])).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      (((k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.20/0.52         (k10_relat_1 @ sk_A @ sk_C))
% 0.20/0.52         = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['51', '61'])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['18', '24'])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (((k10_relat_1 @ sk_A @ sk_C)
% 0.20/0.52         = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.20/0.52      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.52  thf('65', plain,
% 0.20/0.52      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.20/0.52         (((k10_relat_1 @ (k7_relat_1 @ X48 @ X47) @ X49)
% 0.20/0.52            = (k1_setfam_1 @ (k2_tarski @ X47 @ (k10_relat_1 @ X48 @ X49))))
% 0.20/0.52          | ~ (v1_relat_1 @ X48))),
% 0.20/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf('66', plain,
% 0.20/0.52      (((k10_relat_1 @ sk_A @ sk_C)
% 0.20/0.52         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('67', plain,
% 0.20/0.52      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.20/0.52          != (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))
% 0.20/0.52        | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.52  thf('68', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      (((k10_relat_1 @ sk_A @ sk_C)
% 0.20/0.52         != (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.20/0.52      inference('demod', [status(thm)], ['67', '68'])).
% 0.20/0.52  thf('70', plain, ($false),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['64', '69'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

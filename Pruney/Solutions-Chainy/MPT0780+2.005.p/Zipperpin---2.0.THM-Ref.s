%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RjxNdIZCgH

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:25 EST 2020

% Result     : Theorem 0.92s
% Output     : Refutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 111 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :   19
%              Number of atoms          :  659 ( 929 expanded)
%              Number of equality atoms :   33 (  43 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t29_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
          = ( k2_wellord1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
            = ( k2_wellord1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_wellord1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t19_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k3_relat_1 @ ( k2_wellord1 @ C @ B ) ) )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k3_relat_1 @ ( k2_wellord1 @ X29 @ X30 ) ) )
      | ( r2_hidden @ X28 @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t19_wellord1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X19: $i] :
      ( ( ( k3_relat_1 @ X19 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X19 ) @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('16',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ( ( k7_relat_1 @ X22 @ X23 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('20',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X31 @ X33 ) @ X32 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X31 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf('21',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X19: $i] :
      ( ( ( k3_relat_1 @ X19 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X19 ) @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('38',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ( ( k8_relat_1 @ X21 @ X20 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf(t17_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ) )).

thf('42',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_wellord1 @ X27 @ X26 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X26 @ X27 ) @ X26 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ sk_B ) @ sk_A )
 != ( k2_wellord1 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k7_relat_1 @ ( k2_wellord1 @ sk_C_1 @ sk_A ) @ sk_B )
     != ( k2_wellord1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ( k7_relat_1 @ ( k2_wellord1 @ sk_C_1 @ sk_A ) @ sk_B )
 != ( k2_wellord1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k2_wellord1 @ sk_C_1 @ sk_A )
     != ( k2_wellord1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ( k2_wellord1 @ sk_C_1 @ sk_A )
 != ( k2_wellord1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(simplify,[status(thm)],['54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RjxNdIZCgH
% 0.16/0.36  % Computer   : n016.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 13:03:34 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.92/1.16  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.92/1.16  % Solved by: fo/fo7.sh
% 0.92/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.92/1.16  % done 1068 iterations in 0.723s
% 0.92/1.16  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.92/1.16  % SZS output start Refutation
% 0.92/1.16  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.92/1.16  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.92/1.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.92/1.16  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.92/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.92/1.16  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.92/1.16  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.92/1.16  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.92/1.16  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.92/1.16  thf(sk_B_type, type, sk_B: $i).
% 0.92/1.16  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.92/1.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.92/1.16  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.92/1.16  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.92/1.16  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.92/1.16  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.92/1.16  thf(t29_wellord1, conjecture,
% 0.92/1.16    (![A:$i,B:$i,C:$i]:
% 0.92/1.16     ( ( v1_relat_1 @ C ) =>
% 0.92/1.16       ( ( r1_tarski @ A @ B ) =>
% 0.92/1.16         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.92/1.16           ( k2_wellord1 @ C @ A ) ) ) ))).
% 0.92/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.92/1.16    (~( ![A:$i,B:$i,C:$i]:
% 0.92/1.16        ( ( v1_relat_1 @ C ) =>
% 0.92/1.16          ( ( r1_tarski @ A @ B ) =>
% 0.92/1.16            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.92/1.16              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 0.92/1.16    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 0.92/1.16  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.92/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.16  thf(d3_tarski, axiom,
% 0.92/1.16    (![A:$i,B:$i]:
% 0.92/1.16     ( ( r1_tarski @ A @ B ) <=>
% 0.92/1.16       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.92/1.16  thf('1', plain,
% 0.92/1.16      (![X1 : $i, X3 : $i]:
% 0.92/1.16         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.92/1.16      inference('cnf', [status(esa)], [d3_tarski])).
% 0.92/1.16  thf(t19_wellord1, axiom,
% 0.92/1.16    (![A:$i,B:$i,C:$i]:
% 0.92/1.16     ( ( v1_relat_1 @ C ) =>
% 0.92/1.16       ( ( r2_hidden @ A @ ( k3_relat_1 @ ( k2_wellord1 @ C @ B ) ) ) =>
% 0.92/1.16         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & ( r2_hidden @ A @ B ) ) ) ))).
% 0.92/1.16  thf('2', plain,
% 0.92/1.16      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.92/1.16         (~ (r2_hidden @ X28 @ (k3_relat_1 @ (k2_wellord1 @ X29 @ X30)))
% 0.92/1.16          | (r2_hidden @ X28 @ X30)
% 0.92/1.16          | ~ (v1_relat_1 @ X29))),
% 0.92/1.16      inference('cnf', [status(esa)], [t19_wellord1])).
% 0.92/1.16  thf('3', plain,
% 0.92/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.16         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 0.92/1.16          | ~ (v1_relat_1 @ X1)
% 0.92/1.16          | (r2_hidden @ 
% 0.92/1.16             (sk_C @ X2 @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0))) @ X0))),
% 0.92/1.16      inference('sup-', [status(thm)], ['1', '2'])).
% 0.92/1.16  thf('4', plain,
% 0.92/1.16      (![X1 : $i, X3 : $i]:
% 0.92/1.16         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.92/1.16      inference('cnf', [status(esa)], [d3_tarski])).
% 0.92/1.16  thf('5', plain,
% 0.92/1.16      (![X0 : $i, X1 : $i]:
% 0.92/1.16         (~ (v1_relat_1 @ X1)
% 0.92/1.16          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.92/1.16          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0))),
% 0.92/1.16      inference('sup-', [status(thm)], ['3', '4'])).
% 0.92/1.16  thf('6', plain,
% 0.92/1.16      (![X0 : $i, X1 : $i]:
% 0.92/1.16         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.92/1.16          | ~ (v1_relat_1 @ X1))),
% 0.92/1.16      inference('simplify', [status(thm)], ['5'])).
% 0.92/1.16  thf(d6_relat_1, axiom,
% 0.92/1.16    (![A:$i]:
% 0.92/1.16     ( ( v1_relat_1 @ A ) =>
% 0.92/1.16       ( ( k3_relat_1 @ A ) =
% 0.92/1.16         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.92/1.16  thf('7', plain,
% 0.92/1.16      (![X19 : $i]:
% 0.92/1.16         (((k3_relat_1 @ X19)
% 0.92/1.16            = (k2_xboole_0 @ (k1_relat_1 @ X19) @ (k2_relat_1 @ X19)))
% 0.92/1.16          | ~ (v1_relat_1 @ X19))),
% 0.92/1.16      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.92/1.16  thf(t11_xboole_1, axiom,
% 0.92/1.16    (![A:$i,B:$i,C:$i]:
% 0.92/1.16     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.92/1.16  thf('8', plain,
% 0.92/1.16      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.92/1.16         ((r1_tarski @ X4 @ X5) | ~ (r1_tarski @ (k2_xboole_0 @ X4 @ X6) @ X5))),
% 0.92/1.16      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.92/1.16  thf('9', plain,
% 0.92/1.16      (![X0 : $i, X1 : $i]:
% 0.92/1.16         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 0.92/1.16          | ~ (v1_relat_1 @ X0)
% 0.92/1.16          | (r1_tarski @ (k1_relat_1 @ X0) @ X1))),
% 0.92/1.16      inference('sup-', [status(thm)], ['7', '8'])).
% 0.92/1.16  thf('10', plain,
% 0.92/1.16      (![X0 : $i, X1 : $i]:
% 0.92/1.16         (~ (v1_relat_1 @ X1)
% 0.92/1.16          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.92/1.16          | ~ (v1_relat_1 @ (k2_wellord1 @ X1 @ X0)))),
% 0.92/1.16      inference('sup-', [status(thm)], ['6', '9'])).
% 0.92/1.16  thf(dt_k2_wellord1, axiom,
% 0.92/1.16    (![A:$i,B:$i]:
% 0.92/1.16     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ))).
% 0.92/1.16  thf('11', plain,
% 0.92/1.16      (![X24 : $i, X25 : $i]:
% 0.92/1.16         (~ (v1_relat_1 @ X24) | (v1_relat_1 @ (k2_wellord1 @ X24 @ X25)))),
% 0.92/1.16      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.92/1.16  thf('12', plain,
% 0.92/1.16      (![X0 : $i, X1 : $i]:
% 0.92/1.16         ((r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.92/1.16          | ~ (v1_relat_1 @ X1))),
% 0.92/1.16      inference('clc', [status(thm)], ['10', '11'])).
% 0.92/1.16  thf(t1_xboole_1, axiom,
% 0.92/1.16    (![A:$i,B:$i,C:$i]:
% 0.92/1.16     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.92/1.16       ( r1_tarski @ A @ C ) ))).
% 0.92/1.16  thf('13', plain,
% 0.92/1.16      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.92/1.16         (~ (r1_tarski @ X7 @ X8)
% 0.92/1.16          | ~ (r1_tarski @ X8 @ X9)
% 0.92/1.16          | (r1_tarski @ X7 @ X9))),
% 0.92/1.16      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.92/1.16  thf('14', plain,
% 0.92/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.16         (~ (v1_relat_1 @ X1)
% 0.92/1.16          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 0.92/1.16          | ~ (r1_tarski @ X0 @ X2))),
% 0.92/1.16      inference('sup-', [status(thm)], ['12', '13'])).
% 0.92/1.16  thf('15', plain,
% 0.92/1.16      (![X0 : $i]:
% 0.92/1.16         ((r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.92/1.16          | ~ (v1_relat_1 @ X0))),
% 0.92/1.16      inference('sup-', [status(thm)], ['0', '14'])).
% 0.92/1.16  thf(t97_relat_1, axiom,
% 0.92/1.16    (![A:$i,B:$i]:
% 0.92/1.16     ( ( v1_relat_1 @ B ) =>
% 0.92/1.16       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.92/1.16         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.92/1.16  thf('16', plain,
% 0.92/1.16      (![X22 : $i, X23 : $i]:
% 0.92/1.16         (~ (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 0.92/1.16          | ((k7_relat_1 @ X22 @ X23) = (X22))
% 0.92/1.16          | ~ (v1_relat_1 @ X22))),
% 0.92/1.16      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.92/1.16  thf('17', plain,
% 0.92/1.16      (![X0 : $i]:
% 0.92/1.16         (~ (v1_relat_1 @ X0)
% 0.92/1.16          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 0.92/1.16          | ((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.92/1.16              = (k2_wellord1 @ X0 @ sk_A)))),
% 0.92/1.16      inference('sup-', [status(thm)], ['15', '16'])).
% 0.92/1.16  thf('18', plain,
% 0.92/1.16      (![X24 : $i, X25 : $i]:
% 0.92/1.16         (~ (v1_relat_1 @ X24) | (v1_relat_1 @ (k2_wellord1 @ X24 @ X25)))),
% 0.92/1.16      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.92/1.16  thf('19', plain,
% 0.92/1.16      (![X0 : $i]:
% 0.92/1.16         (((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.92/1.16            = (k2_wellord1 @ X0 @ sk_A))
% 0.92/1.16          | ~ (v1_relat_1 @ X0))),
% 0.92/1.16      inference('clc', [status(thm)], ['17', '18'])).
% 0.92/1.16  thf(t27_wellord1, axiom,
% 0.92/1.16    (![A:$i,B:$i,C:$i]:
% 0.92/1.16     ( ( v1_relat_1 @ C ) =>
% 0.92/1.16       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.92/1.16         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 0.92/1.16  thf('20', plain,
% 0.92/1.16      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.92/1.16         (((k2_wellord1 @ (k2_wellord1 @ X31 @ X33) @ X32)
% 0.92/1.16            = (k2_wellord1 @ (k2_wellord1 @ X31 @ X32) @ X33))
% 0.92/1.16          | ~ (v1_relat_1 @ X31))),
% 0.92/1.16      inference('cnf', [status(esa)], [t27_wellord1])).
% 0.92/1.16  thf('21', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.92/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.16  thf('22', plain,
% 0.92/1.16      (![X0 : $i, X1 : $i]:
% 0.92/1.16         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.92/1.16          | ~ (v1_relat_1 @ X1))),
% 0.92/1.16      inference('simplify', [status(thm)], ['5'])).
% 0.92/1.16  thf('23', plain,
% 0.92/1.16      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.92/1.16         (~ (r1_tarski @ X7 @ X8)
% 0.92/1.16          | ~ (r1_tarski @ X8 @ X9)
% 0.92/1.16          | (r1_tarski @ X7 @ X9))),
% 0.92/1.16      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.92/1.16  thf('24', plain,
% 0.92/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.16         (~ (v1_relat_1 @ X1)
% 0.92/1.16          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 0.92/1.16          | ~ (r1_tarski @ X0 @ X2))),
% 0.92/1.16      inference('sup-', [status(thm)], ['22', '23'])).
% 0.92/1.16  thf('25', plain,
% 0.92/1.16      (![X0 : $i]:
% 0.92/1.16         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.92/1.16          | ~ (v1_relat_1 @ X0))),
% 0.92/1.16      inference('sup-', [status(thm)], ['21', '24'])).
% 0.92/1.16  thf('26', plain,
% 0.92/1.16      (![X19 : $i]:
% 0.92/1.16         (((k3_relat_1 @ X19)
% 0.92/1.16            = (k2_xboole_0 @ (k1_relat_1 @ X19) @ (k2_relat_1 @ X19)))
% 0.92/1.16          | ~ (v1_relat_1 @ X19))),
% 0.92/1.16      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.92/1.16  thf(commutativity_k2_tarski, axiom,
% 0.92/1.16    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.92/1.16  thf('27', plain,
% 0.92/1.16      (![X10 : $i, X11 : $i]:
% 0.92/1.16         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.92/1.16      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.92/1.16  thf(l51_zfmisc_1, axiom,
% 0.92/1.16    (![A:$i,B:$i]:
% 0.92/1.16     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.92/1.16  thf('28', plain,
% 0.92/1.16      (![X17 : $i, X18 : $i]:
% 0.92/1.16         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 0.92/1.16      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.92/1.16  thf('29', plain,
% 0.92/1.16      (![X0 : $i, X1 : $i]:
% 0.92/1.16         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.92/1.16      inference('sup+', [status(thm)], ['27', '28'])).
% 0.92/1.16  thf('30', plain,
% 0.92/1.16      (![X17 : $i, X18 : $i]:
% 0.92/1.16         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 0.92/1.16      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.92/1.16  thf('31', plain,
% 0.92/1.16      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.92/1.16      inference('sup+', [status(thm)], ['29', '30'])).
% 0.92/1.16  thf('32', plain,
% 0.92/1.16      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.92/1.16         ((r1_tarski @ X4 @ X5) | ~ (r1_tarski @ (k2_xboole_0 @ X4 @ X6) @ X5))),
% 0.92/1.16      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.92/1.16  thf('33', plain,
% 0.92/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.16         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2) | (r1_tarski @ X0 @ X2))),
% 0.92/1.16      inference('sup-', [status(thm)], ['31', '32'])).
% 0.92/1.16  thf('34', plain,
% 0.92/1.16      (![X0 : $i, X1 : $i]:
% 0.92/1.16         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 0.92/1.16          | ~ (v1_relat_1 @ X0)
% 0.92/1.16          | (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.92/1.16      inference('sup-', [status(thm)], ['26', '33'])).
% 0.92/1.16  thf('35', plain,
% 0.92/1.16      (![X0 : $i]:
% 0.92/1.16         (~ (v1_relat_1 @ X0)
% 0.92/1.16          | (r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.92/1.16          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 0.92/1.16      inference('sup-', [status(thm)], ['25', '34'])).
% 0.92/1.16  thf('36', plain,
% 0.92/1.16      (![X24 : $i, X25 : $i]:
% 0.92/1.16         (~ (v1_relat_1 @ X24) | (v1_relat_1 @ (k2_wellord1 @ X24 @ X25)))),
% 0.92/1.16      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.92/1.16  thf('37', plain,
% 0.92/1.16      (![X0 : $i]:
% 0.92/1.16         ((r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.92/1.16          | ~ (v1_relat_1 @ X0))),
% 0.92/1.16      inference('clc', [status(thm)], ['35', '36'])).
% 0.92/1.16  thf(t125_relat_1, axiom,
% 0.92/1.16    (![A:$i,B:$i]:
% 0.92/1.16     ( ( v1_relat_1 @ B ) =>
% 0.92/1.16       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.92/1.16         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.92/1.16  thf('38', plain,
% 0.92/1.16      (![X20 : $i, X21 : $i]:
% 0.92/1.16         (~ (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 0.92/1.16          | ((k8_relat_1 @ X21 @ X20) = (X20))
% 0.92/1.16          | ~ (v1_relat_1 @ X20))),
% 0.92/1.16      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.92/1.16  thf('39', plain,
% 0.92/1.16      (![X0 : $i]:
% 0.92/1.16         (~ (v1_relat_1 @ X0)
% 0.92/1.16          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 0.92/1.16          | ((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 0.92/1.16              = (k2_wellord1 @ X0 @ sk_A)))),
% 0.92/1.16      inference('sup-', [status(thm)], ['37', '38'])).
% 0.92/1.16  thf('40', plain,
% 0.92/1.16      (![X24 : $i, X25 : $i]:
% 0.92/1.16         (~ (v1_relat_1 @ X24) | (v1_relat_1 @ (k2_wellord1 @ X24 @ X25)))),
% 0.92/1.16      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.92/1.16  thf('41', plain,
% 0.92/1.16      (![X0 : $i]:
% 0.92/1.16         (((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 0.92/1.16            = (k2_wellord1 @ X0 @ sk_A))
% 0.92/1.16          | ~ (v1_relat_1 @ X0))),
% 0.92/1.16      inference('clc', [status(thm)], ['39', '40'])).
% 0.92/1.16  thf(t17_wellord1, axiom,
% 0.92/1.16    (![A:$i,B:$i]:
% 0.92/1.16     ( ( v1_relat_1 @ B ) =>
% 0.92/1.16       ( ( k2_wellord1 @ B @ A ) = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ))).
% 0.92/1.16  thf('42', plain,
% 0.92/1.16      (![X26 : $i, X27 : $i]:
% 0.92/1.16         (((k2_wellord1 @ X27 @ X26)
% 0.92/1.16            = (k7_relat_1 @ (k8_relat_1 @ X26 @ X27) @ X26))
% 0.92/1.16          | ~ (v1_relat_1 @ X27))),
% 0.92/1.16      inference('cnf', [status(esa)], [t17_wellord1])).
% 0.92/1.16  thf('43', plain,
% 0.92/1.16      (![X0 : $i]:
% 0.92/1.16         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.92/1.16            = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B))
% 0.92/1.16          | ~ (v1_relat_1 @ X0)
% 0.92/1.16          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 0.92/1.16      inference('sup+', [status(thm)], ['41', '42'])).
% 0.92/1.16  thf('44', plain,
% 0.92/1.16      (![X24 : $i, X25 : $i]:
% 0.92/1.16         (~ (v1_relat_1 @ X24) | (v1_relat_1 @ (k2_wellord1 @ X24 @ X25)))),
% 0.92/1.16      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.92/1.16  thf('45', plain,
% 0.92/1.16      (![X0 : $i]:
% 0.92/1.16         (~ (v1_relat_1 @ X0)
% 0.92/1.16          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.92/1.16              = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)))),
% 0.92/1.16      inference('clc', [status(thm)], ['43', '44'])).
% 0.92/1.16  thf('46', plain,
% 0.92/1.16      (![X0 : $i]:
% 0.92/1.16         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 0.92/1.16            = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B))
% 0.92/1.16          | ~ (v1_relat_1 @ X0)
% 0.92/1.16          | ~ (v1_relat_1 @ X0))),
% 0.92/1.16      inference('sup+', [status(thm)], ['20', '45'])).
% 0.92/1.16  thf('47', plain,
% 0.92/1.16      (![X0 : $i]:
% 0.92/1.16         (~ (v1_relat_1 @ X0)
% 0.92/1.16          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 0.92/1.16              = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)))),
% 0.92/1.16      inference('simplify', [status(thm)], ['46'])).
% 0.92/1.16  thf('48', plain,
% 0.92/1.16      (((k2_wellord1 @ (k2_wellord1 @ sk_C_1 @ sk_B) @ sk_A)
% 0.92/1.16         != (k2_wellord1 @ sk_C_1 @ sk_A))),
% 0.92/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.16  thf('49', plain,
% 0.92/1.16      ((((k7_relat_1 @ (k2_wellord1 @ sk_C_1 @ sk_A) @ sk_B)
% 0.92/1.16          != (k2_wellord1 @ sk_C_1 @ sk_A))
% 0.92/1.16        | ~ (v1_relat_1 @ sk_C_1))),
% 0.92/1.16      inference('sup-', [status(thm)], ['47', '48'])).
% 0.92/1.16  thf('50', plain, ((v1_relat_1 @ sk_C_1)),
% 0.92/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.16  thf('51', plain,
% 0.92/1.16      (((k7_relat_1 @ (k2_wellord1 @ sk_C_1 @ sk_A) @ sk_B)
% 0.92/1.16         != (k2_wellord1 @ sk_C_1 @ sk_A))),
% 0.92/1.16      inference('demod', [status(thm)], ['49', '50'])).
% 0.92/1.16  thf('52', plain,
% 0.92/1.16      ((((k2_wellord1 @ sk_C_1 @ sk_A) != (k2_wellord1 @ sk_C_1 @ sk_A))
% 0.92/1.16        | ~ (v1_relat_1 @ sk_C_1))),
% 0.92/1.16      inference('sup-', [status(thm)], ['19', '51'])).
% 0.92/1.16  thf('53', plain, ((v1_relat_1 @ sk_C_1)),
% 0.92/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.16  thf('54', plain,
% 0.92/1.16      (((k2_wellord1 @ sk_C_1 @ sk_A) != (k2_wellord1 @ sk_C_1 @ sk_A))),
% 0.92/1.16      inference('demod', [status(thm)], ['52', '53'])).
% 0.92/1.16  thf('55', plain, ($false), inference('simplify', [status(thm)], ['54'])).
% 0.92/1.16  
% 0.92/1.16  % SZS output end Refutation
% 0.92/1.16  
% 0.92/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

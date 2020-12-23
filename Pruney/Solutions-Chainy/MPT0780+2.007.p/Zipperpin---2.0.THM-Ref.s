%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6XvuKVW81I

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:26 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 117 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :   19
%              Number of atoms          :  650 ( 966 expanded)
%              Number of equality atoms :   33 (  43 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k3_relat_1 @ ( k2_wellord1 @ X28 @ X29 ) ) )
      | ( r2_hidden @ X27 @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
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

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X18: $i] :
      ( ( ( k3_relat_1 @ X18 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X18 ) @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( ( k8_relat_1 @ X20 @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('28',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X30 @ X32 ) @ X31 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X30 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf('30',plain,(
    ! [X18: $i] :
      ( ( ( k3_relat_1 @ X18 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X18 ) @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('38',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ( ( k7_relat_1 @ X21 @ X22 )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf(t18_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf('42',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_wellord1 @ X26 @ X25 )
        = ( k8_relat_1 @ X25 @ ( k7_relat_1 @ X26 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t18_wellord1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ sk_B ) @ sk_A )
 != ( k2_wellord1 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ sk_C_1 @ sk_A ) )
     != ( k2_wellord1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ sk_C_1 @ sk_A ) )
 != ( k2_wellord1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k2_wellord1 @ sk_C_1 @ sk_A )
     != ( k2_wellord1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['27','51'])).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6XvuKVW81I
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:04:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.06/1.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.06/1.25  % Solved by: fo/fo7.sh
% 1.06/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.25  % done 1057 iterations in 0.793s
% 1.06/1.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.06/1.25  % SZS output start Refutation
% 1.06/1.25  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.06/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.25  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.06/1.25  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.06/1.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.06/1.25  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.25  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 1.06/1.25  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.06/1.25  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.06/1.25  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.06/1.25  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 1.06/1.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.25  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.06/1.25  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.06/1.25  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.06/1.25  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.06/1.25  thf(t29_wellord1, conjecture,
% 1.06/1.25    (![A:$i,B:$i,C:$i]:
% 1.06/1.25     ( ( v1_relat_1 @ C ) =>
% 1.06/1.25       ( ( r1_tarski @ A @ B ) =>
% 1.06/1.25         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 1.06/1.25           ( k2_wellord1 @ C @ A ) ) ) ))).
% 1.06/1.25  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.25    (~( ![A:$i,B:$i,C:$i]:
% 1.06/1.25        ( ( v1_relat_1 @ C ) =>
% 1.06/1.25          ( ( r1_tarski @ A @ B ) =>
% 1.06/1.25            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 1.06/1.25              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 1.06/1.25    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 1.06/1.25  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf(d3_tarski, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( r1_tarski @ A @ B ) <=>
% 1.06/1.25       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.06/1.25  thf('1', plain,
% 1.06/1.25      (![X1 : $i, X3 : $i]:
% 1.06/1.25         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.06/1.25      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.25  thf(t19_wellord1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i]:
% 1.06/1.25     ( ( v1_relat_1 @ C ) =>
% 1.06/1.25       ( ( r2_hidden @ A @ ( k3_relat_1 @ ( k2_wellord1 @ C @ B ) ) ) =>
% 1.06/1.25         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & ( r2_hidden @ A @ B ) ) ) ))).
% 1.06/1.25  thf('2', plain,
% 1.06/1.25      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.06/1.25         (~ (r2_hidden @ X27 @ (k3_relat_1 @ (k2_wellord1 @ X28 @ X29)))
% 1.06/1.25          | (r2_hidden @ X27 @ X29)
% 1.06/1.25          | ~ (v1_relat_1 @ X28))),
% 1.06/1.25      inference('cnf', [status(esa)], [t19_wellord1])).
% 1.06/1.25  thf('3', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.25         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 1.06/1.25          | ~ (v1_relat_1 @ X1)
% 1.06/1.25          | (r2_hidden @ 
% 1.06/1.25             (sk_C @ X2 @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0))) @ X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['1', '2'])).
% 1.06/1.25  thf('4', plain,
% 1.06/1.25      (![X1 : $i, X3 : $i]:
% 1.06/1.25         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.06/1.25      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.25  thf('5', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         (~ (v1_relat_1 @ X1)
% 1.06/1.25          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 1.06/1.25          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['3', '4'])).
% 1.06/1.25  thf('6', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 1.06/1.25          | ~ (v1_relat_1 @ X1))),
% 1.06/1.25      inference('simplify', [status(thm)], ['5'])).
% 1.06/1.25  thf(t1_xboole_1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i]:
% 1.06/1.25     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.06/1.25       ( r1_tarski @ A @ C ) ))).
% 1.06/1.25  thf('7', plain,
% 1.06/1.25      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.06/1.25         (~ (r1_tarski @ X4 @ X5)
% 1.06/1.25          | ~ (r1_tarski @ X5 @ X6)
% 1.06/1.25          | (r1_tarski @ X4 @ X6))),
% 1.06/1.25      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.06/1.25  thf('8', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.25         (~ (v1_relat_1 @ X1)
% 1.06/1.25          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 1.06/1.25          | ~ (r1_tarski @ X0 @ X2))),
% 1.06/1.25      inference('sup-', [status(thm)], ['6', '7'])).
% 1.06/1.25  thf('9', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 1.06/1.25          | ~ (v1_relat_1 @ X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['0', '8'])).
% 1.06/1.25  thf(d6_relat_1, axiom,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( v1_relat_1 @ A ) =>
% 1.06/1.25       ( ( k3_relat_1 @ A ) =
% 1.06/1.25         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.06/1.25  thf('10', plain,
% 1.06/1.25      (![X18 : $i]:
% 1.06/1.25         (((k3_relat_1 @ X18)
% 1.06/1.25            = (k2_xboole_0 @ (k1_relat_1 @ X18) @ (k2_relat_1 @ X18)))
% 1.06/1.25          | ~ (v1_relat_1 @ X18))),
% 1.06/1.25      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.06/1.25  thf(commutativity_k2_tarski, axiom,
% 1.06/1.25    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.06/1.25  thf('11', plain,
% 1.06/1.25      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 1.06/1.25      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.06/1.25  thf(l51_zfmisc_1, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.06/1.25  thf('12', plain,
% 1.06/1.25      (![X16 : $i, X17 : $i]:
% 1.06/1.25         ((k3_tarski @ (k2_tarski @ X16 @ X17)) = (k2_xboole_0 @ X16 @ X17))),
% 1.06/1.25      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.06/1.25  thf('13', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.06/1.25      inference('sup+', [status(thm)], ['11', '12'])).
% 1.06/1.25  thf('14', plain,
% 1.06/1.25      (![X16 : $i, X17 : $i]:
% 1.06/1.25         ((k3_tarski @ (k2_tarski @ X16 @ X17)) = (k2_xboole_0 @ X16 @ X17))),
% 1.06/1.25      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.06/1.25  thf('15', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.06/1.25      inference('sup+', [status(thm)], ['13', '14'])).
% 1.06/1.25  thf(t7_xboole_1, axiom,
% 1.06/1.25    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.06/1.25  thf('16', plain,
% 1.06/1.25      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 1.06/1.25      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.06/1.25  thf('17', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.06/1.25      inference('sup+', [status(thm)], ['15', '16'])).
% 1.06/1.25  thf('18', plain,
% 1.06/1.25      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.06/1.25         (~ (r1_tarski @ X4 @ X5)
% 1.06/1.25          | ~ (r1_tarski @ X5 @ X6)
% 1.06/1.25          | (r1_tarski @ X4 @ X6))),
% 1.06/1.25      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.06/1.25  thf('19', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.25         ((r1_tarski @ X0 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 1.06/1.25      inference('sup-', [status(thm)], ['17', '18'])).
% 1.06/1.25  thf('20', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 1.06/1.25          | ~ (v1_relat_1 @ X0)
% 1.06/1.25          | (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 1.06/1.25      inference('sup-', [status(thm)], ['10', '19'])).
% 1.06/1.25  thf('21', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (v1_relat_1 @ X0)
% 1.06/1.25          | (r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 1.06/1.25          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['9', '20'])).
% 1.06/1.25  thf(dt_k2_wellord1, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ))).
% 1.06/1.25  thf('22', plain,
% 1.06/1.25      (![X23 : $i, X24 : $i]:
% 1.06/1.25         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k2_wellord1 @ X23 @ X24)))),
% 1.06/1.25      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 1.06/1.25  thf('23', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 1.06/1.25          | ~ (v1_relat_1 @ X0))),
% 1.06/1.25      inference('clc', [status(thm)], ['21', '22'])).
% 1.06/1.25  thf(t125_relat_1, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( v1_relat_1 @ B ) =>
% 1.06/1.25       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.06/1.25         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 1.06/1.25  thf('24', plain,
% 1.06/1.25      (![X19 : $i, X20 : $i]:
% 1.06/1.25         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 1.06/1.25          | ((k8_relat_1 @ X20 @ X19) = (X19))
% 1.06/1.25          | ~ (v1_relat_1 @ X19))),
% 1.06/1.25      inference('cnf', [status(esa)], [t125_relat_1])).
% 1.06/1.25  thf('25', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (v1_relat_1 @ X0)
% 1.06/1.25          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 1.06/1.25          | ((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 1.06/1.25              = (k2_wellord1 @ X0 @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['23', '24'])).
% 1.06/1.25  thf('26', plain,
% 1.06/1.25      (![X23 : $i, X24 : $i]:
% 1.06/1.25         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k2_wellord1 @ X23 @ X24)))),
% 1.06/1.25      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 1.06/1.25  thf('27', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 1.06/1.25            = (k2_wellord1 @ X0 @ sk_A))
% 1.06/1.25          | ~ (v1_relat_1 @ X0))),
% 1.06/1.25      inference('clc', [status(thm)], ['25', '26'])).
% 1.06/1.25  thf(t27_wellord1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i]:
% 1.06/1.25     ( ( v1_relat_1 @ C ) =>
% 1.06/1.25       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 1.06/1.25         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 1.06/1.25  thf('28', plain,
% 1.06/1.25      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.06/1.25         (((k2_wellord1 @ (k2_wellord1 @ X30 @ X32) @ X31)
% 1.06/1.25            = (k2_wellord1 @ (k2_wellord1 @ X30 @ X31) @ X32))
% 1.06/1.25          | ~ (v1_relat_1 @ X30))),
% 1.06/1.25      inference('cnf', [status(esa)], [t27_wellord1])).
% 1.06/1.25  thf('29', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 1.06/1.25          | ~ (v1_relat_1 @ X0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['0', '8'])).
% 1.06/1.25  thf('30', plain,
% 1.06/1.25      (![X18 : $i]:
% 1.06/1.25         (((k3_relat_1 @ X18)
% 1.06/1.25            = (k2_xboole_0 @ (k1_relat_1 @ X18) @ (k2_relat_1 @ X18)))
% 1.06/1.25          | ~ (v1_relat_1 @ X18))),
% 1.06/1.25      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.06/1.25  thf('31', plain,
% 1.06/1.25      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 1.06/1.25      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.06/1.25  thf('32', plain,
% 1.06/1.25      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.06/1.25         (~ (r1_tarski @ X4 @ X5)
% 1.06/1.25          | ~ (r1_tarski @ X5 @ X6)
% 1.06/1.25          | (r1_tarski @ X4 @ X6))),
% 1.06/1.25      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.06/1.25  thf('33', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.25         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 1.06/1.25      inference('sup-', [status(thm)], ['31', '32'])).
% 1.06/1.25  thf('34', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 1.06/1.25          | ~ (v1_relat_1 @ X0)
% 1.06/1.25          | (r1_tarski @ (k1_relat_1 @ X0) @ X1))),
% 1.06/1.25      inference('sup-', [status(thm)], ['30', '33'])).
% 1.06/1.25  thf('35', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (v1_relat_1 @ X0)
% 1.06/1.25          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 1.06/1.25          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['29', '34'])).
% 1.06/1.25  thf('36', plain,
% 1.06/1.25      (![X23 : $i, X24 : $i]:
% 1.06/1.25         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k2_wellord1 @ X23 @ X24)))),
% 1.06/1.25      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 1.06/1.25  thf('37', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 1.06/1.25          | ~ (v1_relat_1 @ X0))),
% 1.06/1.25      inference('clc', [status(thm)], ['35', '36'])).
% 1.06/1.25  thf(t97_relat_1, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( v1_relat_1 @ B ) =>
% 1.06/1.25       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.06/1.25         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 1.06/1.25  thf('38', plain,
% 1.06/1.25      (![X21 : $i, X22 : $i]:
% 1.06/1.25         (~ (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 1.06/1.25          | ((k7_relat_1 @ X21 @ X22) = (X21))
% 1.06/1.25          | ~ (v1_relat_1 @ X21))),
% 1.06/1.25      inference('cnf', [status(esa)], [t97_relat_1])).
% 1.06/1.25  thf('39', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (v1_relat_1 @ X0)
% 1.06/1.25          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 1.06/1.25          | ((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 1.06/1.25              = (k2_wellord1 @ X0 @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['37', '38'])).
% 1.06/1.25  thf('40', plain,
% 1.06/1.25      (![X23 : $i, X24 : $i]:
% 1.06/1.25         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k2_wellord1 @ X23 @ X24)))),
% 1.06/1.25      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 1.06/1.25  thf('41', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 1.06/1.25            = (k2_wellord1 @ X0 @ sk_A))
% 1.06/1.25          | ~ (v1_relat_1 @ X0))),
% 1.06/1.25      inference('clc', [status(thm)], ['39', '40'])).
% 1.06/1.25  thf(t18_wellord1, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( v1_relat_1 @ B ) =>
% 1.06/1.25       ( ( k2_wellord1 @ B @ A ) = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ))).
% 1.06/1.25  thf('42', plain,
% 1.06/1.25      (![X25 : $i, X26 : $i]:
% 1.06/1.25         (((k2_wellord1 @ X26 @ X25)
% 1.06/1.25            = (k8_relat_1 @ X25 @ (k7_relat_1 @ X26 @ X25)))
% 1.06/1.25          | ~ (v1_relat_1 @ X26))),
% 1.06/1.25      inference('cnf', [status(esa)], [t18_wellord1])).
% 1.06/1.25  thf('43', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 1.06/1.25            = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A)))
% 1.06/1.25          | ~ (v1_relat_1 @ X0)
% 1.06/1.25          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 1.06/1.25      inference('sup+', [status(thm)], ['41', '42'])).
% 1.06/1.25  thf('44', plain,
% 1.06/1.25      (![X23 : $i, X24 : $i]:
% 1.06/1.25         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k2_wellord1 @ X23 @ X24)))),
% 1.06/1.25      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 1.06/1.25  thf('45', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (v1_relat_1 @ X0)
% 1.06/1.25          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 1.06/1.25              = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))))),
% 1.06/1.25      inference('clc', [status(thm)], ['43', '44'])).
% 1.06/1.25  thf('46', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 1.06/1.25            = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A)))
% 1.06/1.25          | ~ (v1_relat_1 @ X0)
% 1.06/1.25          | ~ (v1_relat_1 @ X0))),
% 1.06/1.25      inference('sup+', [status(thm)], ['28', '45'])).
% 1.06/1.25  thf('47', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (v1_relat_1 @ X0)
% 1.06/1.25          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 1.06/1.25              = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))))),
% 1.06/1.25      inference('simplify', [status(thm)], ['46'])).
% 1.06/1.25  thf('48', plain,
% 1.06/1.25      (((k2_wellord1 @ (k2_wellord1 @ sk_C_1 @ sk_B) @ sk_A)
% 1.06/1.25         != (k2_wellord1 @ sk_C_1 @ sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('49', plain,
% 1.06/1.25      ((((k8_relat_1 @ sk_B @ (k2_wellord1 @ sk_C_1 @ sk_A))
% 1.06/1.25          != (k2_wellord1 @ sk_C_1 @ sk_A))
% 1.06/1.25        | ~ (v1_relat_1 @ sk_C_1))),
% 1.06/1.25      inference('sup-', [status(thm)], ['47', '48'])).
% 1.06/1.25  thf('50', plain, ((v1_relat_1 @ sk_C_1)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('51', plain,
% 1.06/1.25      (((k8_relat_1 @ sk_B @ (k2_wellord1 @ sk_C_1 @ sk_A))
% 1.06/1.25         != (k2_wellord1 @ sk_C_1 @ sk_A))),
% 1.06/1.25      inference('demod', [status(thm)], ['49', '50'])).
% 1.06/1.25  thf('52', plain,
% 1.06/1.25      ((((k2_wellord1 @ sk_C_1 @ sk_A) != (k2_wellord1 @ sk_C_1 @ sk_A))
% 1.06/1.25        | ~ (v1_relat_1 @ sk_C_1))),
% 1.06/1.25      inference('sup-', [status(thm)], ['27', '51'])).
% 1.06/1.25  thf('53', plain, ((v1_relat_1 @ sk_C_1)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('54', plain,
% 1.06/1.25      (((k2_wellord1 @ sk_C_1 @ sk_A) != (k2_wellord1 @ sk_C_1 @ sk_A))),
% 1.06/1.25      inference('demod', [status(thm)], ['52', '53'])).
% 1.06/1.25  thf('55', plain, ($false), inference('simplify', [status(thm)], ['54'])).
% 1.06/1.25  
% 1.06/1.25  % SZS output end Refutation
% 1.06/1.25  
% 1.06/1.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

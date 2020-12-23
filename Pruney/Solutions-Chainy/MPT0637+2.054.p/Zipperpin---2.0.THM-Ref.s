%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1mMIjNRBJa

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:03 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  172 (1321 expanded)
%              Number of leaves         :   25 ( 475 expanded)
%              Depth                    :   21
%              Number of atoms          : 1574 (11753 expanded)
%              Number of equality atoms :  115 ( 911 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k8_relat_1 @ X15 @ X14 )
        = ( k5_relat_1 @ X14 @ ( k6_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

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

thf('2',plain,
    ( ( ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k8_relat_1 @ X15 @ X14 )
        = ( k5_relat_1 @ X14 @ ( k6_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('7',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X26 ) @ X25 )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ X18 @ X19 )
        = ( k7_relat_1 @ X18 @ ( k3_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k8_relat_1 @ X15 @ X14 )
        = ( k5_relat_1 @ X14 @ ( k6_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('22',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k7_relat_1 @ X28 @ X27 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['20','26','27'])).

thf('29',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t124_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('30',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k8_relat_1 @ X17 @ X16 )
        = ( k3_xboole_0 @ X16 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X16 ) @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t124_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k8_relat_1 @ X17 @ X16 )
        = ( k3_xboole_0 @ X16 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X16 ) @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t124_relat_1])).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k6_relat_1 @ X1 )
        = ( k3_xboole_0 @ ( k6_relat_1 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('48',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k6_relat_1 @ X1 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['44','45','46','47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','49'])).

thf('51',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['20','26','27'])).

thf('56',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k7_relat_1 @ X28 @ X27 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k8_relat_1 @ X15 @ X14 )
        = ( k5_relat_1 @ X14 @ ( k6_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('58',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X26 ) @ X25 )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','62'])).

thf('64',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) @ X22 )
        = ( k5_relat_1 @ X21 @ ( k5_relat_1 @ X20 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('69',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['57','70'])).

thf('72',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('73',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k8_relat_1 @ X15 @ X14 )
        = ( k5_relat_1 @ X14 @ ( k6_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('76',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) @ X22 )
        = ( k5_relat_1 @ X21 @ ( k5_relat_1 @ X20 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('82',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k8_relat_1 @ X15 @ X14 )
        = ( k5_relat_1 @ X14 @ ( k6_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('83',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) @ X22 )
        = ( k5_relat_1 @ X21 @ ( k5_relat_1 @ X20 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('89',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('90',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['87','88','89','90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('95',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k8_relat_1 @ X15 @ X14 )
        = ( k5_relat_1 @ X14 @ ( k6_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('98',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('99',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('100',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['96','97','98','99','100'])).

thf('102',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('103',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['93','101','102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['74','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['56','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('108',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['106','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['20','26','27'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k7_relat_1 @ X28 @ X27 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['93','101','102','103'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X2 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('121',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('122',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['93','101','102','103'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['93','101','102','103'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['119','120','121','122','123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['116','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['115','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['54','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['20','26','27'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k8_relat_1 @ X17 @ X16 )
        = ( k3_xboole_0 @ X16 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X16 ) @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t124_relat_1])).

thf('135',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['133','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('144',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','143'])).

thf('145',plain,(
    $false ),
    inference(simplify,[status(thm)],['144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1mMIjNRBJa
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 12:47:00 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.43/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.68  % Solved by: fo/fo7.sh
% 0.43/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.68  % done 295 iterations in 0.205s
% 0.43/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.68  % SZS output start Refutation
% 0.43/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.43/0.68  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.43/0.68  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.43/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.68  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.43/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.43/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.43/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.68  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.43/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.43/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.68  thf(t123_relat_1, axiom,
% 0.43/0.68    (![A:$i,B:$i]:
% 0.43/0.68     ( ( v1_relat_1 @ B ) =>
% 0.43/0.68       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.43/0.68  thf('0', plain,
% 0.43/0.68      (![X14 : $i, X15 : $i]:
% 0.43/0.68         (((k8_relat_1 @ X15 @ X14) = (k5_relat_1 @ X14 @ (k6_relat_1 @ X15)))
% 0.43/0.68          | ~ (v1_relat_1 @ X14))),
% 0.43/0.68      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.43/0.68  thf(t43_funct_1, conjecture,
% 0.43/0.68    (![A:$i,B:$i]:
% 0.43/0.68     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.43/0.68       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.43/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.68    (~( ![A:$i,B:$i]:
% 0.43/0.68        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.43/0.68          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.43/0.68    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.43/0.68  thf('1', plain,
% 0.43/0.68      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.43/0.68         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.43/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.68  thf('2', plain,
% 0.43/0.68      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.43/0.68          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.43/0.68        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.43/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.43/0.68  thf(fc3_funct_1, axiom,
% 0.43/0.68    (![A:$i]:
% 0.43/0.68     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.43/0.68       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.43/0.68  thf('3', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('4', plain,
% 0.43/0.68      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.43/0.68         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.43/0.68      inference('demod', [status(thm)], ['2', '3'])).
% 0.43/0.68  thf('5', plain,
% 0.43/0.68      (![X14 : $i, X15 : $i]:
% 0.43/0.68         (((k8_relat_1 @ X15 @ X14) = (k5_relat_1 @ X14 @ (k6_relat_1 @ X15)))
% 0.43/0.68          | ~ (v1_relat_1 @ X14))),
% 0.43/0.68      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.43/0.68  thf(t17_xboole_1, axiom,
% 0.43/0.68    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.43/0.68  thf('6', plain,
% 0.43/0.68      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.43/0.68      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.43/0.68  thf(t71_relat_1, axiom,
% 0.43/0.68    (![A:$i]:
% 0.43/0.68     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.43/0.68       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.43/0.68  thf('7', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.43/0.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.43/0.68  thf(t77_relat_1, axiom,
% 0.43/0.68    (![A:$i,B:$i]:
% 0.43/0.68     ( ( v1_relat_1 @ B ) =>
% 0.43/0.68       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.43/0.68         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.43/0.68  thf('8', plain,
% 0.43/0.68      (![X25 : $i, X26 : $i]:
% 0.43/0.68         (~ (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 0.43/0.68          | ((k5_relat_1 @ (k6_relat_1 @ X26) @ X25) = (X25))
% 0.43/0.68          | ~ (v1_relat_1 @ X25))),
% 0.43/0.68      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.43/0.68  thf('9', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (~ (r1_tarski @ X0 @ X1)
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.43/0.68          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.43/0.68              = (k6_relat_1 @ X0)))),
% 0.43/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.43/0.68  thf('10', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('11', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (~ (r1_tarski @ X0 @ X1)
% 0.43/0.68          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.43/0.68              = (k6_relat_1 @ X0)))),
% 0.43/0.68      inference('demod', [status(thm)], ['9', '10'])).
% 0.43/0.68  thf('12', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.43/0.68           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 0.43/0.68           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.43/0.68      inference('sup-', [status(thm)], ['6', '11'])).
% 0.43/0.68  thf('13', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (((k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X0))
% 0.43/0.68            = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.43/0.68      inference('sup+', [status(thm)], ['5', '12'])).
% 0.43/0.68  thf('14', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('15', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X0))
% 0.43/0.68           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.43/0.68      inference('demod', [status(thm)], ['13', '14'])).
% 0.43/0.68  thf('16', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.43/0.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.43/0.68  thf(t192_relat_1, axiom,
% 0.43/0.68    (![A:$i,B:$i]:
% 0.43/0.68     ( ( v1_relat_1 @ B ) =>
% 0.43/0.68       ( ( k7_relat_1 @ B @ A ) =
% 0.43/0.68         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.43/0.68  thf('17', plain,
% 0.43/0.68      (![X18 : $i, X19 : $i]:
% 0.43/0.68         (((k7_relat_1 @ X18 @ X19)
% 0.43/0.68            = (k7_relat_1 @ X18 @ (k3_xboole_0 @ (k1_relat_1 @ X18) @ X19)))
% 0.43/0.68          | ~ (v1_relat_1 @ X18))),
% 0.43/0.68      inference('cnf', [status(esa)], [t192_relat_1])).
% 0.43/0.68  thf('18', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.43/0.68            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.43/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.43/0.68  thf('19', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('20', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.43/0.68           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.43/0.68      inference('demod', [status(thm)], ['18', '19'])).
% 0.43/0.68  thf('21', plain,
% 0.43/0.68      (![X14 : $i, X15 : $i]:
% 0.43/0.68         (((k8_relat_1 @ X15 @ X14) = (k5_relat_1 @ X14 @ (k6_relat_1 @ X15)))
% 0.43/0.68          | ~ (v1_relat_1 @ X14))),
% 0.43/0.68      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.43/0.68  thf(t94_relat_1, axiom,
% 0.43/0.68    (![A:$i,B:$i]:
% 0.43/0.68     ( ( v1_relat_1 @ B ) =>
% 0.43/0.68       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.43/0.68  thf('22', plain,
% 0.43/0.68      (![X27 : $i, X28 : $i]:
% 0.43/0.68         (((k7_relat_1 @ X28 @ X27) = (k5_relat_1 @ (k6_relat_1 @ X27) @ X28))
% 0.43/0.68          | ~ (v1_relat_1 @ X28))),
% 0.43/0.68      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.43/0.68  thf('23', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.43/0.68            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.43/0.68      inference('sup+', [status(thm)], ['21', '22'])).
% 0.43/0.68  thf('24', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('25', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('26', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.43/0.68           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.43/0.68      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.43/0.68  thf('27', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.43/0.68           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.43/0.68      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.43/0.68  thf('28', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.43/0.68           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.43/0.68      inference('demod', [status(thm)], ['20', '26', '27'])).
% 0.43/0.68  thf('29', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.43/0.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.43/0.68  thf(t124_relat_1, axiom,
% 0.43/0.68    (![A:$i,B:$i]:
% 0.43/0.68     ( ( v1_relat_1 @ B ) =>
% 0.43/0.68       ( ( k8_relat_1 @ A @ B ) =
% 0.43/0.68         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.43/0.68  thf('30', plain,
% 0.43/0.68      (![X16 : $i, X17 : $i]:
% 0.43/0.68         (((k8_relat_1 @ X17 @ X16)
% 0.43/0.68            = (k3_xboole_0 @ X16 @ (k2_zfmisc_1 @ (k1_relat_1 @ X16) @ X17)))
% 0.43/0.68          | ~ (v1_relat_1 @ X16))),
% 0.43/0.68      inference('cnf', [status(esa)], [t124_relat_1])).
% 0.43/0.68  thf('31', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.43/0.68            = (k3_xboole_0 @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.43/0.68      inference('sup+', [status(thm)], ['29', '30'])).
% 0.43/0.68  thf('32', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('33', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.43/0.68           = (k3_xboole_0 @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 0.43/0.68      inference('demod', [status(thm)], ['31', '32'])).
% 0.43/0.68  thf('34', plain,
% 0.43/0.68      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.43/0.68      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.43/0.68  thf('35', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))),
% 0.43/0.68      inference('sup+', [status(thm)], ['33', '34'])).
% 0.43/0.68  thf('36', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 0.43/0.68          (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.43/0.68      inference('sup+', [status(thm)], ['28', '35'])).
% 0.43/0.68  thf('37', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (r1_tarski @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.43/0.68          (k6_relat_1 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 0.43/0.68      inference('sup+', [status(thm)], ['15', '36'])).
% 0.43/0.68  thf('38', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X0))
% 0.43/0.68           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.43/0.68      inference('demod', [status(thm)], ['13', '14'])).
% 0.43/0.68  thf('39', plain,
% 0.43/0.68      (![X16 : $i, X17 : $i]:
% 0.43/0.68         (((k8_relat_1 @ X17 @ X16)
% 0.43/0.68            = (k3_xboole_0 @ X16 @ (k2_zfmisc_1 @ (k1_relat_1 @ X16) @ X17)))
% 0.43/0.68          | ~ (v1_relat_1 @ X16))),
% 0.43/0.68      inference('cnf', [status(esa)], [t124_relat_1])).
% 0.43/0.68  thf('40', plain,
% 0.43/0.68      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.43/0.68      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.43/0.68  thf(d10_xboole_0, axiom,
% 0.43/0.68    (![A:$i,B:$i]:
% 0.43/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.43/0.68  thf('41', plain,
% 0.43/0.68      (![X0 : $i, X2 : $i]:
% 0.43/0.68         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.43/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.68  thf('42', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.43/0.68          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.43/0.68      inference('sup-', [status(thm)], ['40', '41'])).
% 0.43/0.68  thf('43', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (~ (r1_tarski @ X0 @ (k8_relat_1 @ X1 @ X0))
% 0.43/0.68          | ~ (v1_relat_1 @ X0)
% 0.43/0.68          | ((X0) = (k3_xboole_0 @ X0 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1))))),
% 0.43/0.68      inference('sup-', [status(thm)], ['39', '42'])).
% 0.43/0.68  thf('44', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (~ (r1_tarski @ (k6_relat_1 @ X1) @ 
% 0.43/0.68             (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.43/0.68          | ((k6_relat_1 @ X1)
% 0.43/0.68              = (k3_xboole_0 @ (k6_relat_1 @ X1) @ 
% 0.43/0.68                 (k2_zfmisc_1 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ 
% 0.43/0.68                  (k3_xboole_0 @ X1 @ X0))))
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.43/0.68      inference('sup-', [status(thm)], ['38', '43'])).
% 0.43/0.68  thf('45', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.43/0.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.43/0.68  thf('46', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.43/0.68           = (k3_xboole_0 @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 0.43/0.68      inference('demod', [status(thm)], ['31', '32'])).
% 0.43/0.68  thf('47', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X0))
% 0.43/0.68           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.43/0.68      inference('demod', [status(thm)], ['13', '14'])).
% 0.43/0.68  thf('48', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('49', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (~ (r1_tarski @ (k6_relat_1 @ X1) @ 
% 0.43/0.68             (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.43/0.68          | ((k6_relat_1 @ X1) = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.43/0.68      inference('demod', [status(thm)], ['44', '45', '46', '47', '48'])).
% 0.43/0.68  thf('50', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 0.43/0.68           = (k6_relat_1 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)))),
% 0.43/0.68      inference('sup-', [status(thm)], ['37', '49'])).
% 0.43/0.68  thf('51', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.43/0.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.43/0.68  thf('52', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.43/0.68           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.43/0.68      inference('sup+', [status(thm)], ['50', '51'])).
% 0.43/0.68  thf('53', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.43/0.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.43/0.68  thf('54', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k3_xboole_0 @ X1 @ X0)
% 0.43/0.68           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.43/0.68      inference('demod', [status(thm)], ['52', '53'])).
% 0.43/0.68  thf('55', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.43/0.68           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.43/0.68      inference('demod', [status(thm)], ['20', '26', '27'])).
% 0.43/0.68  thf('56', plain,
% 0.43/0.68      (![X27 : $i, X28 : $i]:
% 0.43/0.68         (((k7_relat_1 @ X28 @ X27) = (k5_relat_1 @ (k6_relat_1 @ X27) @ X28))
% 0.43/0.68          | ~ (v1_relat_1 @ X28))),
% 0.43/0.68      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.43/0.68  thf('57', plain,
% 0.43/0.68      (![X14 : $i, X15 : $i]:
% 0.43/0.68         (((k8_relat_1 @ X15 @ X14) = (k5_relat_1 @ X14 @ (k6_relat_1 @ X15)))
% 0.43/0.68          | ~ (v1_relat_1 @ X14))),
% 0.43/0.68      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.43/0.68  thf('58', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.43/0.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.43/0.68  thf('59', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.43/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.68  thf('60', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.43/0.68      inference('simplify', [status(thm)], ['59'])).
% 0.43/0.68  thf('61', plain,
% 0.43/0.68      (![X25 : $i, X26 : $i]:
% 0.43/0.68         (~ (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 0.43/0.68          | ((k5_relat_1 @ (k6_relat_1 @ X26) @ X25) = (X25))
% 0.43/0.68          | ~ (v1_relat_1 @ X25))),
% 0.43/0.68      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.43/0.68  thf('62', plain,
% 0.43/0.68      (![X0 : $i]:
% 0.43/0.68         (~ (v1_relat_1 @ X0)
% 0.43/0.68          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 0.43/0.68      inference('sup-', [status(thm)], ['60', '61'])).
% 0.43/0.68  thf('63', plain,
% 0.43/0.68      (![X0 : $i]:
% 0.43/0.68         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.43/0.68            = (k6_relat_1 @ X0))
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.43/0.68      inference('sup+', [status(thm)], ['58', '62'])).
% 0.43/0.68  thf('64', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('65', plain,
% 0.43/0.68      (![X0 : $i]:
% 0.43/0.68         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.43/0.68           = (k6_relat_1 @ X0))),
% 0.43/0.68      inference('demod', [status(thm)], ['63', '64'])).
% 0.43/0.68  thf(t55_relat_1, axiom,
% 0.43/0.68    (![A:$i]:
% 0.43/0.68     ( ( v1_relat_1 @ A ) =>
% 0.43/0.68       ( ![B:$i]:
% 0.43/0.68         ( ( v1_relat_1 @ B ) =>
% 0.43/0.68           ( ![C:$i]:
% 0.43/0.68             ( ( v1_relat_1 @ C ) =>
% 0.43/0.68               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.43/0.68                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.43/0.68  thf('66', plain,
% 0.43/0.68      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.43/0.68         (~ (v1_relat_1 @ X20)
% 0.43/0.68          | ((k5_relat_1 @ (k5_relat_1 @ X21 @ X20) @ X22)
% 0.43/0.68              = (k5_relat_1 @ X21 @ (k5_relat_1 @ X20 @ X22)))
% 0.43/0.68          | ~ (v1_relat_1 @ X22)
% 0.43/0.68          | ~ (v1_relat_1 @ X21))),
% 0.43/0.68      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.43/0.68  thf('67', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.43/0.68            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.43/0.68               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.43/0.68          | ~ (v1_relat_1 @ X1)
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.43/0.68      inference('sup+', [status(thm)], ['65', '66'])).
% 0.43/0.68  thf('68', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('69', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('70', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (((k5_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.43/0.68            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.43/0.68               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.43/0.68          | ~ (v1_relat_1 @ X1))),
% 0.43/0.68      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.43/0.68  thf('71', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.43/0.68            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.43/0.68               (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.43/0.68      inference('sup+', [status(thm)], ['57', '70'])).
% 0.43/0.68  thf('72', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('73', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('74', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.43/0.68           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.43/0.68              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.43/0.68      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.43/0.68  thf('75', plain,
% 0.43/0.68      (![X14 : $i, X15 : $i]:
% 0.43/0.68         (((k8_relat_1 @ X15 @ X14) = (k5_relat_1 @ X14 @ (k6_relat_1 @ X15)))
% 0.43/0.68          | ~ (v1_relat_1 @ X14))),
% 0.43/0.68      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.43/0.68  thf('76', plain,
% 0.43/0.68      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.43/0.68         (~ (v1_relat_1 @ X20)
% 0.43/0.68          | ((k5_relat_1 @ (k5_relat_1 @ X21 @ X20) @ X22)
% 0.43/0.68              = (k5_relat_1 @ X21 @ (k5_relat_1 @ X20 @ X22)))
% 0.43/0.68          | ~ (v1_relat_1 @ X22)
% 0.43/0.68          | ~ (v1_relat_1 @ X21))),
% 0.43/0.68      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.43/0.68  thf('77', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.68         (((k5_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.43/0.68            = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X2)))
% 0.43/0.68          | ~ (v1_relat_1 @ X0)
% 0.43/0.68          | ~ (v1_relat_1 @ X0)
% 0.43/0.68          | ~ (v1_relat_1 @ X2)
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.43/0.68      inference('sup+', [status(thm)], ['75', '76'])).
% 0.43/0.68  thf('78', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('79', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.68         (((k5_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.43/0.68            = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X2)))
% 0.43/0.68          | ~ (v1_relat_1 @ X0)
% 0.43/0.68          | ~ (v1_relat_1 @ X0)
% 0.43/0.68          | ~ (v1_relat_1 @ X2))),
% 0.43/0.68      inference('demod', [status(thm)], ['77', '78'])).
% 0.43/0.68  thf('80', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.68         (~ (v1_relat_1 @ X2)
% 0.43/0.68          | ~ (v1_relat_1 @ X0)
% 0.43/0.68          | ((k5_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.43/0.68              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X2))))),
% 0.43/0.68      inference('simplify', [status(thm)], ['79'])).
% 0.43/0.68  thf('81', plain,
% 0.43/0.68      (![X0 : $i]:
% 0.43/0.68         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.43/0.68           = (k6_relat_1 @ X0))),
% 0.43/0.68      inference('demod', [status(thm)], ['63', '64'])).
% 0.43/0.68  thf('82', plain,
% 0.43/0.68      (![X14 : $i, X15 : $i]:
% 0.43/0.68         (((k8_relat_1 @ X15 @ X14) = (k5_relat_1 @ X14 @ (k6_relat_1 @ X15)))
% 0.43/0.68          | ~ (v1_relat_1 @ X14))),
% 0.43/0.68      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.43/0.68  thf('83', plain,
% 0.43/0.68      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.43/0.68         (~ (v1_relat_1 @ X20)
% 0.43/0.68          | ((k5_relat_1 @ (k5_relat_1 @ X21 @ X20) @ X22)
% 0.43/0.68              = (k5_relat_1 @ X21 @ (k5_relat_1 @ X20 @ X22)))
% 0.43/0.68          | ~ (v1_relat_1 @ X22)
% 0.43/0.68          | ~ (v1_relat_1 @ X21))),
% 0.43/0.68      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.43/0.68  thf('84', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.68         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.68            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 0.43/0.68          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.68          | ~ (v1_relat_1 @ X1)
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X2))
% 0.43/0.68          | ~ (v1_relat_1 @ X0))),
% 0.43/0.68      inference('sup+', [status(thm)], ['82', '83'])).
% 0.43/0.68  thf('85', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('86', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.68         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.68            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 0.43/0.68          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.68          | ~ (v1_relat_1 @ X1)
% 0.43/0.68          | ~ (v1_relat_1 @ X0))),
% 0.43/0.68      inference('demod', [status(thm)], ['84', '85'])).
% 0.43/0.68  thf('87', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.43/0.68          | ((k8_relat_1 @ X1 @ 
% 0.43/0.68              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0)))
% 0.43/0.68              = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.43/0.68                 (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))))),
% 0.43/0.68      inference('sup-', [status(thm)], ['81', '86'])).
% 0.43/0.68  thf('88', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('89', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('90', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('91', plain,
% 0.43/0.68      (![X0 : $i]:
% 0.43/0.68         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.43/0.68           = (k6_relat_1 @ X0))),
% 0.43/0.68      inference('demod', [status(thm)], ['63', '64'])).
% 0.43/0.68  thf('92', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.43/0.68           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.43/0.68              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))))),
% 0.43/0.68      inference('demod', [status(thm)], ['87', '88', '89', '90', '91'])).
% 0.43/0.68  thf('93', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.43/0.68            = (k5_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X1)) @ 
% 0.43/0.68               (k6_relat_1 @ X0)))
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.43/0.68      inference('sup+', [status(thm)], ['80', '92'])).
% 0.43/0.68  thf('94', plain,
% 0.43/0.68      (![X0 : $i]:
% 0.43/0.68         (~ (v1_relat_1 @ X0)
% 0.43/0.68          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 0.43/0.68      inference('sup-', [status(thm)], ['60', '61'])).
% 0.43/0.68  thf('95', plain,
% 0.43/0.68      (![X14 : $i, X15 : $i]:
% 0.43/0.68         (((k8_relat_1 @ X15 @ X14) = (k5_relat_1 @ X14 @ (k6_relat_1 @ X15)))
% 0.43/0.68          | ~ (v1_relat_1 @ X14))),
% 0.43/0.68      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.43/0.68  thf('96', plain,
% 0.43/0.68      (![X0 : $i]:
% 0.43/0.68         (((k8_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0))))
% 0.43/0.68            = (k6_relat_1 @ X0))
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0)))))),
% 0.43/0.68      inference('sup+', [status(thm)], ['94', '95'])).
% 0.43/0.68  thf('97', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.43/0.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.43/0.68  thf('98', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('99', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.43/0.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.43/0.68  thf('100', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('101', plain,
% 0.43/0.68      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.43/0.68      inference('demod', [status(thm)], ['96', '97', '98', '99', '100'])).
% 0.43/0.68  thf('102', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('103', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('104', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.43/0.68           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.43/0.68      inference('demod', [status(thm)], ['93', '101', '102', '103'])).
% 0.43/0.68  thf('105', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.43/0.68           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.43/0.68              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.43/0.68      inference('demod', [status(thm)], ['74', '104'])).
% 0.43/0.68  thf('106', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.43/0.68            = (k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X0))
% 0.43/0.68          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.43/0.68      inference('sup+', [status(thm)], ['56', '105'])).
% 0.43/0.68  thf('107', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.43/0.68           = (k3_xboole_0 @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 0.43/0.68      inference('demod', [status(thm)], ['31', '32'])).
% 0.43/0.68  thf(fc1_relat_1, axiom,
% 0.43/0.68    (![A:$i,B:$i]:
% 0.43/0.68     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.43/0.68  thf('108', plain,
% 0.43/0.68      (![X12 : $i, X13 : $i]:
% 0.43/0.68         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.43/0.68  thf('109', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.43/0.68      inference('sup+', [status(thm)], ['107', '108'])).
% 0.43/0.68  thf('110', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('111', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.43/0.68      inference('demod', [status(thm)], ['109', '110'])).
% 0.43/0.68  thf('112', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.43/0.68           = (k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X0))),
% 0.43/0.68      inference('demod', [status(thm)], ['106', '111'])).
% 0.43/0.68  thf('113', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.43/0.68           = (k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 0.43/0.68              (k3_xboole_0 @ X1 @ X0)))),
% 0.43/0.68      inference('sup+', [status(thm)], ['55', '112'])).
% 0.43/0.68  thf('114', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.43/0.68           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.43/0.68      inference('demod', [status(thm)], ['20', '26', '27'])).
% 0.43/0.68  thf('115', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.43/0.68           = (k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 0.43/0.68              (k3_xboole_0 @ X1 @ X0)))),
% 0.43/0.68      inference('demod', [status(thm)], ['113', '114'])).
% 0.43/0.68  thf('116', plain,
% 0.43/0.68      (![X27 : $i, X28 : $i]:
% 0.43/0.68         (((k7_relat_1 @ X28 @ X27) = (k5_relat_1 @ (k6_relat_1 @ X27) @ X28))
% 0.43/0.68          | ~ (v1_relat_1 @ X28))),
% 0.43/0.68      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.43/0.68  thf('117', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.43/0.68           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.43/0.68      inference('demod', [status(thm)], ['93', '101', '102', '103'])).
% 0.43/0.68  thf('118', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.68         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.68            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 0.43/0.68          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.43/0.68          | ~ (v1_relat_1 @ X1)
% 0.43/0.68          | ~ (v1_relat_1 @ X0))),
% 0.43/0.68      inference('demod', [status(thm)], ['84', '85'])).
% 0.43/0.68  thf('119', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.68         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.43/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.43/0.68          | ((k8_relat_1 @ X2 @ 
% 0.43/0.68              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 0.43/0.68              = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.43/0.68                 (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X2)))))),
% 0.43/0.68      inference('sup-', [status(thm)], ['117', '118'])).
% 0.43/0.68  thf('120', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.43/0.68      inference('demod', [status(thm)], ['109', '110'])).
% 0.43/0.68  thf('121', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('122', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.43/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.43/0.68  thf('123', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.43/0.68           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.43/0.68      inference('demod', [status(thm)], ['93', '101', '102', '103'])).
% 0.43/0.68  thf('124', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.43/0.68           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.43/0.68      inference('demod', [status(thm)], ['93', '101', '102', '103'])).
% 0.43/0.68  thf('125', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.68         ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.43/0.68           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.43/0.68              (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))),
% 0.43/0.68      inference('demod', [status(thm)],
% 0.43/0.68                ['119', '120', '121', '122', '123', '124'])).
% 0.43/0.68  thf('126', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.68         (((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.43/0.68            = (k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0))
% 0.43/0.68          | ~ (v1_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))),
% 0.43/0.68      inference('sup+', [status(thm)], ['116', '125'])).
% 0.43/0.68  thf('127', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.43/0.68      inference('demod', [status(thm)], ['109', '110'])).
% 0.43/0.68  thf('128', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.68         ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.43/0.68           = (k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0))),
% 0.43/0.68      inference('demod', [status(thm)], ['126', '127'])).
% 0.43/0.68  thf('129', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.43/0.68           = (k8_relat_1 @ X1 @ 
% 0.43/0.68              (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))))),
% 0.43/0.68      inference('demod', [status(thm)], ['115', '128'])).
% 0.43/0.68  thf('130', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X1))
% 0.43/0.68           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.43/0.68              (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))))),
% 0.43/0.68      inference('sup+', [status(thm)], ['54', '129'])).
% 0.43/0.68  thf('131', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X0))
% 0.43/0.68           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.43/0.68      inference('demod', [status(thm)], ['13', '14'])).
% 0.43/0.68  thf('132', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.43/0.68           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.43/0.68      inference('demod', [status(thm)], ['20', '26', '27'])).
% 0.43/0.68  thf('133', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.43/0.68           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.43/0.68              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.43/0.68      inference('demod', [status(thm)], ['130', '131', '132'])).
% 0.43/0.68  thf('134', plain,
% 0.43/0.68      (![X16 : $i, X17 : $i]:
% 0.43/0.68         (((k8_relat_1 @ X17 @ X16)
% 0.43/0.68            = (k3_xboole_0 @ X16 @ (k2_zfmisc_1 @ (k1_relat_1 @ X16) @ X17)))
% 0.43/0.68          | ~ (v1_relat_1 @ X16))),
% 0.43/0.68      inference('cnf', [status(esa)], [t124_relat_1])).
% 0.43/0.68  thf('135', plain,
% 0.43/0.68      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.43/0.68      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.43/0.68  thf('136', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0) | ~ (v1_relat_1 @ X0))),
% 0.43/0.68      inference('sup+', [status(thm)], ['134', '135'])).
% 0.43/0.68  thf('137', plain,
% 0.43/0.68      (![X0 : $i, X2 : $i]:
% 0.43/0.68         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.43/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.68  thf('138', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (~ (v1_relat_1 @ X0)
% 0.43/0.68          | ~ (r1_tarski @ X0 @ (k8_relat_1 @ X1 @ X0))
% 0.43/0.68          | ((X0) = (k8_relat_1 @ X1 @ X0)))),
% 0.43/0.68      inference('sup-', [status(thm)], ['136', '137'])).
% 0.43/0.68  thf('139', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (~ (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 0.43/0.68             (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.43/0.68          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.43/0.68              = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.43/0.68                 (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.43/0.68          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.43/0.68      inference('sup-', [status(thm)], ['133', '138'])).
% 0.43/0.68  thf('140', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 0.43/0.68          (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.43/0.68      inference('sup+', [status(thm)], ['28', '35'])).
% 0.43/0.68  thf('141', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.43/0.68           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.43/0.68              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.43/0.68      inference('demod', [status(thm)], ['130', '131', '132'])).
% 0.43/0.68  thf('142', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.43/0.68      inference('demod', [status(thm)], ['109', '110'])).
% 0.43/0.68  thf('143', plain,
% 0.43/0.68      (![X0 : $i, X1 : $i]:
% 0.43/0.68         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.43/0.68           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.43/0.68      inference('demod', [status(thm)], ['139', '140', '141', '142'])).
% 0.43/0.68  thf('144', plain,
% 0.43/0.68      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.43/0.68         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 0.43/0.68      inference('demod', [status(thm)], ['4', '143'])).
% 0.43/0.68  thf('145', plain, ($false), inference('simplify', [status(thm)], ['144'])).
% 0.43/0.68  
% 0.43/0.68  % SZS output end Refutation
% 0.43/0.68  
% 0.43/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

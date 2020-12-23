%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0470+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5IrJY6QVzN

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:56 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  185 (1359 expanded)
%              Number of leaves         :   39 ( 455 expanded)
%              Depth                    :   44
%              Number of atoms          : 1205 (8594 expanded)
%              Number of equality atoms :  128 (1257 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_5_type,type,(
    sk_A_5: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ ( k1_xboole_0 @ A ) )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ ( A @ k1_xboole_0 ) )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ ( k1_xboole_0 @ A ) )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ ( A @ k1_xboole_0 ) )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('0',plain,(
    v1_relat_1 @ sk_A_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ ( A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X2085: $i,X2086: $i] :
      ( ~ ( v1_relat_1 @ X2085 )
      | ~ ( v1_relat_1 @ X2086 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( X2085 @ X2086 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('2',plain,(
    v1_relat_1 @ sk_A_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_tarski @ ( X78 @ X79 ) )
      | ( X78 != X79 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('5',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('6',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k6_subset_1 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( X0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf(t41_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k6_subset_1 @ ( A @ B ) ) )
            = ( k6_subset_1 @ ( k4_relat_1 @ A @ ( k4_relat_1 @ B ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X2153: $i,X2154: $i] :
      ( ~ ( v1_relat_1 @ X2153 )
      | ( ( k4_relat_1 @ ( k6_subset_1 @ ( X2154 @ X2153 ) ) )
        = ( k6_subset_1 @ ( k4_relat_1 @ X2154 @ ( k4_relat_1 @ X2153 ) ) ) )
      | ~ ( v1_relat_1 @ X2154 ) ) ),
    inference(cnf,[status(esa)],[t41_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k6_subset_1 @ ( X0 @ X0 ) ) )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( X0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ o_0_0_xboole_0 )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ o_0_0_xboole_0 )
        = o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( k4_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['2','14'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ ( A @ B ) ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B @ ( k4_relat_1 @ A ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X2182: $i,X2183: $i] :
      ( ~ ( v1_relat_1 @ X2182 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ ( X2183 @ X2182 ) ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X2182 @ ( k4_relat_1 @ X2183 ) ) ) )
      | ~ ( v1_relat_1 @ X2183 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( X0 @ o_0_0_xboole_0 ) ) )
        = ( k5_relat_1 @ ( o_0_0_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('18',plain,(
    ! [X1104: $i,X1105: $i] :
      ( ( ( k2_zfmisc_1 @ ( X1104 @ X1105 ) )
        = k1_xboole_0 )
      | ( X1104 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('19',plain,(
    ! [X1105: $i] :
      ( ( k2_zfmisc_1 @ ( k1_xboole_0 @ X1105 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('21',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('22',plain,(
    ! [X1105: $i] :
      ( ( k2_zfmisc_1 @ ( o_0_0_xboole_0 @ X1105 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) )).

thf('23',plain,(
    ! [X2096: $i,X2097: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ ( X2096 @ X2097 ) ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('24',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( X0 @ o_0_0_xboole_0 ) ) )
        = ( k5_relat_1 @ ( o_0_0_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','24'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('26',plain,(
    ! [X2084: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2084 ) )
      | ~ ( v1_relat_1 @ X2084 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('27',plain,(
    ! [X2085: $i,X2086: $i] :
      ( ~ ( v1_relat_1 @ X2085 )
      | ~ ( v1_relat_1 @ X2086 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( X2085 @ X2086 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('28',plain,(
    ! [X2085: $i,X2086: $i] :
      ( ~ ( v1_relat_1 @ X2085 )
      | ~ ( v1_relat_1 @ X2086 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( X2085 @ X2086 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('29',plain,
    ( ( k4_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['2','14'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( X0 @ o_0_0_xboole_0 ) ) )
        = ( k5_relat_1 @ ( o_0_0_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','24'])).

thf('31',plain,
    ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) )
      = ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('33',plain,
    ( ( k4_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) )
    = ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X2147: $i] :
      ( ( ( k2_relat_1 @ X2147 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X2147 ) ) )
      | ~ ( v1_relat_1 @ X2147 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('35',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k4_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) )
    = ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( X0 @ o_0_0_xboole_0 ) ) )
        = ( k5_relat_1 @ ( o_0_0_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','24'])).

thf('38',plain,(
    ! [X2085: $i,X2086: $i] :
      ( ~ ( v1_relat_1 @ X2085 )
      | ~ ( v1_relat_1 @ X2086 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( X2085 @ X2086 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( X0 @ o_0_0_xboole_0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( X0 @ o_0_0_xboole_0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X2084: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2084 ) )
      | ~ ( v1_relat_1 @ X2084 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( X0 @ o_0_0_xboole_0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v1_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','43'])).

thf('45',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('46',plain,(
    v1_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) )
    = ( k1_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['35','46'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ ( A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('48',plain,(
    ! [X2157: $i,X2158: $i] :
      ( ~ ( v1_relat_1 @ X2157 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ ( X2158 @ X2157 ) ) @ ( k2_relat_1 @ X2157 ) ) )
      | ~ ( v1_relat_1 @ X2158 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('49',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) @ ( k2_relat_1 @ o_0_0_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('50',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('51',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('52',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('53',plain,
    ( ( k2_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('55',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('56',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['49','53','54','55'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ ( A @ k1_xboole_0 ) )
     => ( A = k1_xboole_0 ) ) )).

thf('57',plain,(
    ! [X245: $i] :
      ( ( X245 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X245 @ k1_xboole_0 ) ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('58',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('59',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('60',plain,(
    ! [X245: $i] :
      ( ( X245 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X245 @ o_0_0_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['56','60'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ ( A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A @ ( k2_relat_1 @ A ) ) ) ) )
        = A ) ) )).

thf('62',plain,(
    ! [X2119: $i] :
      ( ( ( k3_xboole_0 @ ( X2119 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X2119 @ ( k2_relat_1 @ X2119 ) ) ) ) )
        = X2119 )
      | ~ ( v1_relat_1 @ X2119 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('63',plain,
    ( ( ( k3_xboole_0 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) @ ( k2_zfmisc_1 @ ( o_0_0_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) ) ) ) ) )
      = ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X1105: $i] :
      ( ( k2_zfmisc_1 @ ( o_0_0_xboole_0 @ X1105 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('65',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ ( A @ k1_xboole_0 ) )
      = k1_xboole_0 ) )).

thf('66',plain,(
    ! [X215: $i] :
      ( ( k3_xboole_0 @ ( X215 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('67',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('68',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('69',plain,(
    ! [X215: $i] :
      ( ( k3_xboole_0 @ ( X215 @ o_0_0_xboole_0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('73',plain,
    ( o_0_0_xboole_0
    = ( k5_relat_1 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['63','64','65','71','72'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ ( A @ B ) @ C ) )
                = ( k5_relat_1 @ ( A @ ( k5_relat_1 @ ( B @ C ) ) ) ) ) ) ) ) )).

thf('74',plain,(
    ! [X2184: $i,X2185: $i,X2186: $i] :
      ( ~ ( v1_relat_1 @ X2184 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( X2185 @ X2184 ) @ X2186 ) )
        = ( k5_relat_1 @ ( X2185 @ ( k5_relat_1 @ ( X2184 @ X2186 ) ) ) ) )
      | ~ ( v1_relat_1 @ X2186 )
      | ~ ( v1_relat_1 @ X2185 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( o_0_0_xboole_0 @ X0 ) )
        = ( k5_relat_1 @ ( o_0_0_xboole_0 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('77',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( o_0_0_xboole_0 @ X0 ) )
        = ( k5_relat_1 @ ( o_0_0_xboole_0 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ) )).

thf('79',plain,(
    ! [X2155: $i,X2156: $i] :
      ( ~ ( v1_relat_1 @ X2155 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( X2156 @ X2155 ) ) @ ( k1_relat_1 @ X2156 ) ) )
      | ~ ( v1_relat_1 @ X2156 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ X0 ) ) @ ( k1_relat_1 @ o_0_0_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('82',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('83',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('84',plain,
    ( ( k1_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ X0 ) ) @ o_0_0_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['80','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ X0 ) ) @ o_0_0_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['28','86'])).

thf('88',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ X0 ) ) @ o_0_0_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ X0 ) ) @ o_0_0_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X245: $i] :
      ( ( X245 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X245 @ o_0_0_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ X0 ) ) )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('93',plain,(
    ! [X2102: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X2102 ) )
      | ~ ( v1_relat_1 @ X2102 )
      | ( v1_xboole_0 @ X2102 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('95',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('96',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('97',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['94','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ o_0_0_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','98'])).

thf('100',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('103',plain,(
    ! [X46: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('104',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('105',plain,(
    ! [X46: $i] :
      ( ( X46 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( o_0_0_xboole_0 @ X0 ) )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( o_0_0_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( X0 @ o_0_0_xboole_0 ) ) )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ ( X0 @ o_0_0_xboole_0 ) ) )
        = o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('110',plain,(
    ! [X2104: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X2104 ) )
        = X2104 )
      | ~ ( v1_relat_1 @ X2104 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ o_0_0_xboole_0 )
        = ( k5_relat_1 @ ( X0 @ o_0_0_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( X0 @ o_0_0_xboole_0 ) ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k4_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['2','14'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0
        = ( k5_relat_1 @ ( X0 @ o_0_0_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( X0 @ o_0_0_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( o_0_0_xboole_0
        = ( k5_relat_1 @ ( X0 @ o_0_0_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','113'])).

thf('115',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( o_0_0_xboole_0
        = ( k5_relat_1 @ ( X0 @ o_0_0_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0
        = ( k5_relat_1 @ ( X0 @ o_0_0_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( o_0_0_xboole_0
    = ( k5_relat_1 @ ( sk_A_5 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','117'])).

thf('119',plain,
    ( ( ( k5_relat_1 @ ( k1_xboole_0 @ sk_A_5 ) )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ ( sk_A_5 @ k1_xboole_0 ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( ( k5_relat_1 @ ( sk_A_5 @ k1_xboole_0 ) )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ ( sk_A_5 @ k1_xboole_0 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['119'])).

thf('121',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('122',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('123',plain,
    ( ( ( k5_relat_1 @ ( sk_A_5 @ o_0_0_xboole_0 ) )
     != o_0_0_xboole_0 )
   <= ( ( k5_relat_1 @ ( sk_A_5 @ k1_xboole_0 ) )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ ( o_0_0_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('125',plain,(
    ! [X392: $i,X393: $i] :
      ( ~ ( v1_xboole_0 @ X392 )
      | ~ ( v1_xboole_0 @ X393 )
      | ( X392 = X393 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('126',plain,(
    ! [X392: $i,X393: $i] :
      ( ~ ( v1_xboole_0 @ X392 )
      | ~ ( v1_xboole_0 @ X393 )
      | ( X392 = X393 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('127',plain,
    ( ( ( k5_relat_1 @ ( k1_xboole_0 @ sk_A_5 ) )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ ( k1_xboole_0 @ sk_A_5 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['119'])).

thf('128',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ ( X0 @ sk_A_5 ) )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ ( k1_xboole_0 @ sk_A_5 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('130',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('131',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['95','96'])).

thf('132',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ ( X0 @ sk_A_5 ) )
         != o_0_0_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ ( k1_xboole_0 @ sk_A_5 ) )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['128','129','130','131'])).

thf('133',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != o_0_0_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ ( X1 @ sk_A_5 ) ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ ( k1_xboole_0 @ sk_A_5 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['125','132'])).

thf('134',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ ( X1 @ sk_A_5 ) ) )
        | ~ ( v1_xboole_0 @ o_0_0_xboole_0 ) )
   <= ( ( k5_relat_1 @ ( k1_xboole_0 @ sk_A_5 ) )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['95','96'])).

thf('136',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ ( X1 @ sk_A_5 ) ) ) )
   <= ( ( k5_relat_1 @ ( k1_xboole_0 @ sk_A_5 ) )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ~ ( v1_relat_1 @ sk_A_5 )
      | ~ ( v1_xboole_0 @ o_0_0_xboole_0 ) )
   <= ( ( k5_relat_1 @ ( k1_xboole_0 @ sk_A_5 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['124','136'])).

thf('138',plain,(
    v1_relat_1 @ sk_A_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['95','96'])).

thf('140',plain,
    ( ( k5_relat_1 @ ( k1_xboole_0 @ sk_A_5 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['137','138','139'])).

thf('141',plain,
    ( ( ( k5_relat_1 @ ( sk_A_5 @ k1_xboole_0 ) )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k1_xboole_0 @ sk_A_5 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['119'])).

thf('142',plain,(
    ( k5_relat_1 @ ( sk_A_5 @ k1_xboole_0 ) )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['140','141'])).

thf('143',plain,(
    ( k5_relat_1 @ ( sk_A_5 @ o_0_0_xboole_0 ) )
 != o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['123','142'])).

thf('144',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['118','143'])).

%------------------------------------------------------------------------------

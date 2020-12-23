%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xP0fdonsqD

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 155 expanded)
%              Number of leaves         :   24 (  54 expanded)
%              Depth                    :   18
%              Number of atoms          :  651 (1112 expanded)
%              Number of equality atoms :   84 ( 163 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X78: $i,X79: $i] :
      ( ~ ( v1_relat_1 @ X78 )
      | ~ ( v1_relat_1 @ X79 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X78 @ X79 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X87: $i,X88: $i] :
      ( ~ ( v1_relat_1 @ X87 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X87 @ X88 ) )
        = ( k2_relat_1 @ X88 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X88 ) @ ( k2_relat_1 @ X87 ) )
      | ~ ( v1_relat_1 @ X88 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k6_subset_1 @ X63 @ X64 )
      = ( k4_xboole_0 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('6',plain,(
    ! [X10: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('8',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k6_subset_1 @ X63 @ X64 )
      = ( k4_xboole_0 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k6_subset_1 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('12',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k2_zfmisc_1 @ X46 @ X47 )
        = k1_xboole_0 )
      | ( X46 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('13',plain,(
    ! [X47: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X47 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X80: $i,X81: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X80 @ X81 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','11','15','16'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('18',plain,(
    ! [X83: $i] :
      ( ( ( k3_xboole_0 @ X83 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X83 ) @ ( k2_relat_1 @ X83 ) ) )
        = X83 )
      | ~ ( v1_relat_1 @ X83 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k2_zfmisc_1 @ X46 @ X47 )
        = k1_xboole_0 )
      | ( X47 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('21',plain,(
    ! [X46: $i] :
      ( ( k2_zfmisc_1 @ X46 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('22',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['19','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','23'])).

thf('25',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('31',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k6_subset_1 @ X63 @ X64 )
      = ( k4_xboole_0 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('32',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k6_subset_1 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k6_subset_1 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k6_subset_1 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('37',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k5_relat_1 @ sk_A_1 @ ( k3_xboole_0 @ X1 @ ( k6_subset_1 @ X0 @ X0 ) ) )
       != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    ! [X78: $i,X79: $i] :
      ( ~ ( v1_relat_1 @ X78 )
      | ~ ( v1_relat_1 @ X79 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X78 @ X79 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('42',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('43',plain,(
    ! [X85: $i,X86: $i] :
      ( ~ ( v1_relat_1 @ X85 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X86 @ X85 ) )
        = ( k1_relat_1 @ X86 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X86 ) @ ( k1_relat_1 @ X85 ) )
      | ~ ( v1_relat_1 @ X86 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('46',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf('47',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,(
    ! [X83: $i] :
      ( ( ( k3_xboole_0 @ X83 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X83 ) @ ( k2_relat_1 @ X83 ) ) )
        = X83 )
      | ~ ( v1_relat_1 @ X83 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X47: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X47 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('52',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','53'])).

thf('55',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf('59',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A_1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf('64',plain,(
    ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['62','63'])).

thf('65',plain,(
    ( k5_relat_1 @ sk_A_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['40','64'])).

thf('66',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['27','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference(simplify,[status(thm)],['68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xP0fdonsqD
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 318 iterations in 0.113s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.57  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.20/0.57  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.57  thf(dt_k5_relat_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.20/0.57       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.20/0.57  thf('0', plain,
% 0.20/0.57      (![X78 : $i, X79 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ X78)
% 0.20/0.57          | ~ (v1_relat_1 @ X79)
% 0.20/0.57          | (v1_relat_1 @ (k5_relat_1 @ X78 @ X79)))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.20/0.57  thf(t60_relat_1, axiom,
% 0.20/0.57    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.57     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.57  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.57  thf(t47_relat_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ A ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( v1_relat_1 @ B ) =>
% 0.20/0.57           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.20/0.57             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      (![X87 : $i, X88 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ X87)
% 0.20/0.57          | ((k2_relat_1 @ (k5_relat_1 @ X87 @ X88)) = (k2_relat_1 @ X88))
% 0.20/0.57          | ~ (r1_tarski @ (k1_relat_1 @ X88) @ (k2_relat_1 @ X87))
% 0.20/0.57          | ~ (v1_relat_1 @ X88))),
% 0.20/0.57      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.20/0.57          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.57          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.57              = (k2_relat_1 @ k1_xboole_0))
% 0.20/0.57          | ~ (v1_relat_1 @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.57  thf(t4_boole, axiom,
% 0.20/0.57    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.57  thf('4', plain,
% 0.20/0.57      (![X10 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.57  thf(redefinition_k6_subset_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      (![X63 : $i, X64 : $i]:
% 0.20/0.57         ((k6_subset_1 @ X63 @ X64) = (k4_xboole_0 @ X63 @ X64))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.57  thf('6', plain,
% 0.20/0.57      (![X10 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.20/0.57      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.57  thf(l32_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.57  thf('7', plain,
% 0.20/0.57      (![X4 : $i, X5 : $i]:
% 0.20/0.57         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.20/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.57  thf('8', plain,
% 0.20/0.57      (![X63 : $i, X64 : $i]:
% 0.20/0.57         ((k6_subset_1 @ X63 @ X64) = (k4_xboole_0 @ X63 @ X64))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.57  thf('9', plain,
% 0.20/0.57      (![X4 : $i, X5 : $i]:
% 0.20/0.57         ((r1_tarski @ X4 @ X5) | ((k6_subset_1 @ X4 @ X5) != (k1_xboole_0)))),
% 0.20/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.57  thf('10', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['6', '9'])).
% 0.20/0.57  thf('11', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.57      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.57  thf(t113_zfmisc_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      (![X46 : $i, X47 : $i]:
% 0.20/0.57         (((k2_zfmisc_1 @ X46 @ X47) = (k1_xboole_0))
% 0.20/0.57          | ((X46) != (k1_xboole_0)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.57  thf('13', plain,
% 0.20/0.57      (![X47 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X47) = (k1_xboole_0))),
% 0.20/0.57      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.57  thf(fc6_relat_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.57  thf('14', plain,
% 0.20/0.57      (![X80 : $i, X81 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X80 @ X81))),
% 0.20/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.57  thf('15', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.57      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.57  thf('16', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.57  thf('17', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.20/0.57          | ~ (v1_relat_1 @ X0))),
% 0.20/0.57      inference('demod', [status(thm)], ['3', '11', '15', '16'])).
% 0.20/0.57  thf(t22_relat_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ A ) =>
% 0.20/0.57       ( ( k3_xboole_0 @
% 0.20/0.57           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.20/0.57         ( A ) ) ))).
% 0.20/0.57  thf('18', plain,
% 0.20/0.57      (![X83 : $i]:
% 0.20/0.57         (((k3_xboole_0 @ X83 @ 
% 0.20/0.57            (k2_zfmisc_1 @ (k1_relat_1 @ X83) @ (k2_relat_1 @ X83))) = (
% 0.20/0.57            X83))
% 0.20/0.57          | ~ (v1_relat_1 @ X83))),
% 0.20/0.57      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.20/0.57  thf('19', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k3_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0) @ 
% 0.20/0.57            (k2_zfmisc_1 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.20/0.57             k1_xboole_0))
% 0.20/0.57            = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.57          | ~ (v1_relat_1 @ X0)
% 0.20/0.57          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.57  thf('20', plain,
% 0.20/0.57      (![X46 : $i, X47 : $i]:
% 0.20/0.57         (((k2_zfmisc_1 @ X46 @ X47) = (k1_xboole_0))
% 0.20/0.57          | ((X47) != (k1_xboole_0)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.57  thf('21', plain,
% 0.20/0.57      (![X46 : $i]: ((k2_zfmisc_1 @ X46 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.57      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.57  thf(t2_boole, axiom,
% 0.20/0.57    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.57  thf('22', plain,
% 0.20/0.57      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.57  thf('23', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.57          | ~ (v1_relat_1 @ X0)
% 0.20/0.57          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.57      inference('demod', [status(thm)], ['19', '21', '22'])).
% 0.20/0.57  thf('24', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.57          | ~ (v1_relat_1 @ X0)
% 0.20/0.57          | ~ (v1_relat_1 @ X0)
% 0.20/0.57          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['0', '23'])).
% 0.20/0.57  thf('25', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.57      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.57  thf('26', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ X0)
% 0.20/0.57          | ~ (v1_relat_1 @ X0)
% 0.20/0.57          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.57      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.57  thf('27', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.57          | ~ (v1_relat_1 @ X0))),
% 0.20/0.57      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.57  thf(d10_xboole_0, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.57  thf('28', plain,
% 0.20/0.57      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.57  thf('29', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.20/0.57      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.57  thf('30', plain,
% 0.20/0.57      (![X4 : $i, X6 : $i]:
% 0.20/0.57         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.57  thf('31', plain,
% 0.20/0.57      (![X63 : $i, X64 : $i]:
% 0.20/0.57         ((k6_subset_1 @ X63 @ X64) = (k4_xboole_0 @ X63 @ X64))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.57  thf('32', plain,
% 0.20/0.57      (![X4 : $i, X6 : $i]:
% 0.20/0.57         (((k6_subset_1 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.57      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.57  thf('33', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['29', '32'])).
% 0.20/0.57  thf('34', plain,
% 0.20/0.57      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.57  thf('35', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k3_xboole_0 @ X1 @ (k6_subset_1 @ X0 @ X0)) = (k1_xboole_0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.57  thf('36', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k3_xboole_0 @ X1 @ (k6_subset_1 @ X0 @ X0)) = (k1_xboole_0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.57  thf(t62_relat_1, conjecture,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ A ) =>
% 0.20/0.57       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.20/0.57         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i]:
% 0.20/0.57        ( ( v1_relat_1 @ A ) =>
% 0.20/0.57          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.20/0.57            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.20/0.57  thf('37', plain,
% 0.20/0.57      ((((k5_relat_1 @ k1_xboole_0 @ sk_A_1) != (k1_xboole_0))
% 0.20/0.57        | ((k5_relat_1 @ sk_A_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('38', plain,
% 0.20/0.57      ((((k5_relat_1 @ sk_A_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.57         <= (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.57      inference('split', [status(esa)], ['37'])).
% 0.20/0.57  thf('39', plain,
% 0.20/0.57      ((![X0 : $i, X1 : $i]:
% 0.20/0.57          ((k5_relat_1 @ sk_A_1 @ (k3_xboole_0 @ X1 @ (k6_subset_1 @ X0 @ X0)))
% 0.20/0.57            != (k1_xboole_0)))
% 0.20/0.57         <= (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['36', '38'])).
% 0.20/0.57  thf('40', plain,
% 0.20/0.57      ((((k5_relat_1 @ sk_A_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.57         <= (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['35', '39'])).
% 0.20/0.57  thf('41', plain,
% 0.20/0.57      (![X78 : $i, X79 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ X78)
% 0.20/0.57          | ~ (v1_relat_1 @ X79)
% 0.20/0.57          | (v1_relat_1 @ (k5_relat_1 @ X78 @ X79)))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.20/0.57  thf('42', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.57  thf(t46_relat_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ A ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( v1_relat_1 @ B ) =>
% 0.20/0.57           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.57             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.57  thf('43', plain,
% 0.20/0.57      (![X85 : $i, X86 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ X85)
% 0.20/0.57          | ((k1_relat_1 @ (k5_relat_1 @ X86 @ X85)) = (k1_relat_1 @ X86))
% 0.20/0.57          | ~ (r1_tarski @ (k2_relat_1 @ X86) @ (k1_relat_1 @ X85))
% 0.20/0.57          | ~ (v1_relat_1 @ X86))),
% 0.20/0.57      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.20/0.57  thf('44', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.20/0.57          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.57          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.57              = (k1_relat_1 @ k1_xboole_0))
% 0.20/0.57          | ~ (v1_relat_1 @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.57  thf('45', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.57      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.57  thf('46', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.57      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.57  thf('47', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.57  thf('48', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.20/0.57          | ~ (v1_relat_1 @ X0))),
% 0.20/0.57      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.20/0.57  thf('49', plain,
% 0.20/0.57      (![X83 : $i]:
% 0.20/0.57         (((k3_xboole_0 @ X83 @ 
% 0.20/0.57            (k2_zfmisc_1 @ (k1_relat_1 @ X83) @ (k2_relat_1 @ X83))) = (
% 0.20/0.57            X83))
% 0.20/0.57          | ~ (v1_relat_1 @ X83))),
% 0.20/0.57      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.20/0.57  thf('50', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k3_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0) @ 
% 0.20/0.57            (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.20/0.57             (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))
% 0.20/0.57            = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.57          | ~ (v1_relat_1 @ X0)
% 0.20/0.57          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['48', '49'])).
% 0.20/0.57  thf('51', plain,
% 0.20/0.57      (![X47 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X47) = (k1_xboole_0))),
% 0.20/0.57      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.57  thf('52', plain,
% 0.20/0.57      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.57  thf('53', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.57          | ~ (v1_relat_1 @ X0)
% 0.20/0.57          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.20/0.57      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.20/0.57  thf('54', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ X0)
% 0.20/0.57          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.57          | ~ (v1_relat_1 @ X0)
% 0.20/0.57          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['41', '53'])).
% 0.20/0.57  thf('55', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.57      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.57  thf('56', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ X0)
% 0.20/0.57          | ~ (v1_relat_1 @ X0)
% 0.20/0.57          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.20/0.57      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.57  thf('57', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.57          | ~ (v1_relat_1 @ X0))),
% 0.20/0.57      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.57  thf('58', plain,
% 0.20/0.57      ((((k5_relat_1 @ k1_xboole_0 @ sk_A_1) != (k1_xboole_0)))
% 0.20/0.57         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0))))),
% 0.20/0.57      inference('split', [status(esa)], ['37'])).
% 0.20/0.57  thf('59', plain,
% 0.20/0.57      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A_1)))
% 0.20/0.57         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.57  thf('60', plain, ((v1_relat_1 @ sk_A_1)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('61', plain,
% 0.20/0.57      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.57         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0))))),
% 0.20/0.57      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.57  thf('62', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['61'])).
% 0.20/0.57  thf('63', plain,
% 0.20/0.57      (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.20/0.57       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0)))),
% 0.20/0.57      inference('split', [status(esa)], ['37'])).
% 0.20/0.57  thf('64', plain, (~ (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.57      inference('sat_resolution*', [status(thm)], ['62', '63'])).
% 0.20/0.57  thf('65', plain, (((k5_relat_1 @ sk_A_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.57      inference('simpl_trail', [status(thm)], ['40', '64'])).
% 0.20/0.57  thf('66', plain,
% 0.20/0.57      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A_1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['27', '65'])).
% 0.20/0.57  thf('67', plain, ((v1_relat_1 @ sk_A_1)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('68', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.57      inference('demod', [status(thm)], ['66', '67'])).
% 0.20/0.57  thf('69', plain, ($false), inference('simplify', [status(thm)], ['68'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.40/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

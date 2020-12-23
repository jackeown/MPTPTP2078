%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X4Veiwq6Tt

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:38 EST 2020

% Result     : Theorem 3.70s
% Output     : Refutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 203 expanded)
%              Number of leaves         :   29 (  75 expanded)
%              Depth                    :   19
%              Number of atoms          :  863 (1550 expanded)
%              Number of equality atoms :   52 ( 106 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X16: $i] :
      ( ( ( k9_relat_1 @ X16 @ ( k1_relat_1 @ X16 ) )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t162_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ B @ C )
           => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
              = ( k9_relat_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t162_relat_1])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('9',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X33 ) @ X34 )
      | ( ( k7_relat_1 @ X33 @ X34 )
        = X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('15',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X27 @ ( k6_relat_1 @ X28 ) ) @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('18',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['13','19'])).

thf(t157_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k9_relat_1 @ X20 @ X21 ) @ ( k9_relat_1 @ X19 @ X21 ) )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t157_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      | ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    r1_tarski @ sk_B @ ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['6','25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_B ) @ sk_B )
    | ( ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_C @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) )
      = ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k9_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ X0 ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('47',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( sk_B
      = ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','48'])).

thf(t159_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('50',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k9_relat_1 @ X22 @ ( k9_relat_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X1 ) @ ( k2_xboole_0 @ sk_C @ X0 ) )
        = ( k9_relat_1 @ X1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X1 ) @ ( k2_xboole_0 @ sk_C @ X0 ) )
        = ( k9_relat_1 @ X1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X27 @ ( k6_relat_1 @ X28 ) ) @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('55',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k9_relat_1 @ X20 @ X21 ) @ ( k9_relat_1 @ X19 @ X21 ) )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t157_relat_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( r1_tarski @ ( k9_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X2 ) @ ( k9_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X2 ) @ ( k9_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X27 @ ( k6_relat_1 @ X28 ) ) @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('59',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('62',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('64',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X2 ) @ ( k9_relat_1 @ X0 @ X2 ) ) ) ),
    inference(clc,[status(thm)],['57','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_xboole_0 @ sk_C @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['53','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( sk_B
      = ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','48'])).

thf('71',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('72',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,
    ( ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['28','73'])).

thf('75',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k9_relat_1 @ X22 @ ( k9_relat_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k9_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( k9_relat_1 @ sk_A @ sk_B )
     != ( k9_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ( k9_relat_1 @ sk_A @ sk_B )
 != ( k9_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    $false ),
    inference(simplify,[status(thm)],['84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X4Veiwq6Tt
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.70/3.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.70/3.89  % Solved by: fo/fo7.sh
% 3.70/3.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.70/3.89  % done 5275 iterations in 3.432s
% 3.70/3.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.70/3.89  % SZS output start Refutation
% 3.70/3.89  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.70/3.89  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.70/3.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.70/3.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.70/3.89  thf(sk_B_type, type, sk_B: $i).
% 3.70/3.89  thf(sk_A_type, type, sk_A: $i).
% 3.70/3.89  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.70/3.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.70/3.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.70/3.89  thf(sk_C_type, type, sk_C: $i).
% 3.70/3.89  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.70/3.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.70/3.89  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.70/3.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.70/3.89  thf(t94_relat_1, axiom,
% 3.70/3.89    (![A:$i,B:$i]:
% 3.70/3.89     ( ( v1_relat_1 @ B ) =>
% 3.70/3.89       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 3.70/3.89  thf('0', plain,
% 3.70/3.89      (![X31 : $i, X32 : $i]:
% 3.70/3.89         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 3.70/3.89          | ~ (v1_relat_1 @ X32))),
% 3.70/3.89      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.70/3.89  thf(t71_relat_1, axiom,
% 3.70/3.89    (![A:$i]:
% 3.70/3.89     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.70/3.89       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.70/3.89  thf('1', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 3.70/3.89      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.70/3.89  thf(t146_relat_1, axiom,
% 3.70/3.89    (![A:$i]:
% 3.70/3.89     ( ( v1_relat_1 @ A ) =>
% 3.70/3.89       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 3.70/3.89  thf('2', plain,
% 3.70/3.89      (![X16 : $i]:
% 3.70/3.89         (((k9_relat_1 @ X16 @ (k1_relat_1 @ X16)) = (k2_relat_1 @ X16))
% 3.70/3.89          | ~ (v1_relat_1 @ X16))),
% 3.70/3.89      inference('cnf', [status(esa)], [t146_relat_1])).
% 3.70/3.89  thf('3', plain,
% 3.70/3.89      (![X0 : $i]:
% 3.70/3.89         (((k9_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 3.70/3.89            = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 3.70/3.89          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.70/3.89      inference('sup+', [status(thm)], ['1', '2'])).
% 3.70/3.89  thf('4', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 3.70/3.89      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.70/3.89  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 3.70/3.89  thf('5', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 3.70/3.89      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.70/3.89  thf('6', plain, (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 3.70/3.89      inference('demod', [status(thm)], ['3', '4', '5'])).
% 3.70/3.89  thf(t162_relat_1, conjecture,
% 3.70/3.89    (![A:$i]:
% 3.70/3.89     ( ( v1_relat_1 @ A ) =>
% 3.70/3.89       ( ![B:$i,C:$i]:
% 3.70/3.89         ( ( r1_tarski @ B @ C ) =>
% 3.70/3.89           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 3.70/3.89             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 3.70/3.89  thf(zf_stmt_0, negated_conjecture,
% 3.70/3.89    (~( ![A:$i]:
% 3.70/3.89        ( ( v1_relat_1 @ A ) =>
% 3.70/3.89          ( ![B:$i,C:$i]:
% 3.70/3.89            ( ( r1_tarski @ B @ C ) =>
% 3.70/3.89              ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 3.70/3.89                ( k9_relat_1 @ A @ B ) ) ) ) ) )),
% 3.70/3.89    inference('cnf.neg', [status(esa)], [t162_relat_1])).
% 3.70/3.89  thf('7', plain, ((r1_tarski @ sk_B @ sk_C)),
% 3.70/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.89  thf('8', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 3.70/3.89      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.70/3.89  thf(t97_relat_1, axiom,
% 3.70/3.89    (![A:$i,B:$i]:
% 3.70/3.89     ( ( v1_relat_1 @ B ) =>
% 3.70/3.89       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 3.70/3.89         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 3.70/3.89  thf('9', plain,
% 3.70/3.89      (![X33 : $i, X34 : $i]:
% 3.70/3.89         (~ (r1_tarski @ (k1_relat_1 @ X33) @ X34)
% 3.70/3.89          | ((k7_relat_1 @ X33 @ X34) = (X33))
% 3.70/3.89          | ~ (v1_relat_1 @ X33))),
% 3.70/3.89      inference('cnf', [status(esa)], [t97_relat_1])).
% 3.70/3.89  thf('10', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i]:
% 3.70/3.89         (~ (r1_tarski @ X0 @ X1)
% 3.70/3.89          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.70/3.89          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 3.70/3.89      inference('sup-', [status(thm)], ['8', '9'])).
% 3.70/3.89  thf('11', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 3.70/3.89      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.70/3.89  thf('12', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i]:
% 3.70/3.89         (~ (r1_tarski @ X0 @ X1)
% 3.70/3.89          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 3.70/3.89      inference('demod', [status(thm)], ['10', '11'])).
% 3.70/3.89  thf('13', plain,
% 3.70/3.89      (((k7_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C) = (k6_relat_1 @ sk_B))),
% 3.70/3.89      inference('sup-', [status(thm)], ['7', '12'])).
% 3.70/3.89  thf('14', plain,
% 3.70/3.89      (![X31 : $i, X32 : $i]:
% 3.70/3.89         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 3.70/3.89          | ~ (v1_relat_1 @ X32))),
% 3.70/3.89      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.70/3.89  thf(t76_relat_1, axiom,
% 3.70/3.89    (![A:$i,B:$i]:
% 3.70/3.89     ( ( v1_relat_1 @ B ) =>
% 3.70/3.89       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 3.70/3.89         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 3.70/3.89  thf('15', plain,
% 3.70/3.89      (![X27 : $i, X28 : $i]:
% 3.70/3.89         ((r1_tarski @ (k5_relat_1 @ X27 @ (k6_relat_1 @ X28)) @ X27)
% 3.70/3.89          | ~ (v1_relat_1 @ X27))),
% 3.70/3.89      inference('cnf', [status(esa)], [t76_relat_1])).
% 3.70/3.89  thf('16', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i]:
% 3.70/3.89         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 3.70/3.89           (k6_relat_1 @ X0))
% 3.70/3.89          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 3.70/3.89          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.70/3.89      inference('sup+', [status(thm)], ['14', '15'])).
% 3.70/3.89  thf('17', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 3.70/3.89      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.70/3.89  thf('18', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 3.70/3.89      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.70/3.89  thf('19', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i]:
% 3.70/3.89         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 3.70/3.89      inference('demod', [status(thm)], ['16', '17', '18'])).
% 3.70/3.89  thf('20', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_C))),
% 3.70/3.89      inference('sup+', [status(thm)], ['13', '19'])).
% 3.70/3.89  thf(t157_relat_1, axiom,
% 3.70/3.89    (![A:$i,B:$i]:
% 3.70/3.89     ( ( v1_relat_1 @ B ) =>
% 3.70/3.89       ( ![C:$i]:
% 3.70/3.89         ( ( v1_relat_1 @ C ) =>
% 3.70/3.89           ( ( r1_tarski @ B @ C ) =>
% 3.70/3.89             ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ))).
% 3.70/3.89  thf('21', plain,
% 3.70/3.89      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.70/3.89         (~ (v1_relat_1 @ X19)
% 3.70/3.89          | (r1_tarski @ (k9_relat_1 @ X20 @ X21) @ (k9_relat_1 @ X19 @ X21))
% 3.70/3.89          | ~ (r1_tarski @ X20 @ X19)
% 3.70/3.89          | ~ (v1_relat_1 @ X20))),
% 3.70/3.89      inference('cnf', [status(esa)], [t157_relat_1])).
% 3.70/3.89  thf('22', plain,
% 3.70/3.89      (![X0 : $i]:
% 3.70/3.89         (~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 3.70/3.89          | (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ 
% 3.70/3.89             (k9_relat_1 @ (k6_relat_1 @ sk_C) @ X0))
% 3.70/3.89          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C)))),
% 3.70/3.89      inference('sup-', [status(thm)], ['20', '21'])).
% 3.70/3.89  thf('23', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 3.70/3.89      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.70/3.89  thf('24', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 3.70/3.89      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.70/3.89  thf('25', plain,
% 3.70/3.89      (![X0 : $i]:
% 3.70/3.89         (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ 
% 3.70/3.89          (k9_relat_1 @ (k6_relat_1 @ sk_C) @ X0))),
% 3.70/3.89      inference('demod', [status(thm)], ['22', '23', '24'])).
% 3.70/3.89  thf('26', plain,
% 3.70/3.89      ((r1_tarski @ sk_B @ (k9_relat_1 @ (k6_relat_1 @ sk_C) @ sk_B))),
% 3.70/3.89      inference('sup+', [status(thm)], ['6', '25'])).
% 3.70/3.89  thf(d10_xboole_0, axiom,
% 3.70/3.89    (![A:$i,B:$i]:
% 3.70/3.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.70/3.89  thf('27', plain,
% 3.70/3.89      (![X0 : $i, X2 : $i]:
% 3.70/3.89         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.70/3.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.70/3.89  thf('28', plain,
% 3.70/3.89      ((~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ sk_C) @ sk_B) @ sk_B)
% 3.70/3.89        | ((k9_relat_1 @ (k6_relat_1 @ sk_C) @ sk_B) = (sk_B)))),
% 3.70/3.89      inference('sup-', [status(thm)], ['26', '27'])).
% 3.70/3.89  thf('29', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.70/3.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.70/3.89  thf('30', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.70/3.89      inference('simplify', [status(thm)], ['29'])).
% 3.70/3.89  thf(t11_xboole_1, axiom,
% 3.70/3.89    (![A:$i,B:$i,C:$i]:
% 3.70/3.89     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 3.70/3.89  thf('31', plain,
% 3.70/3.89      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.70/3.89         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 3.70/3.89      inference('cnf', [status(esa)], [t11_xboole_1])).
% 3.70/3.89  thf('32', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 3.70/3.89      inference('sup-', [status(thm)], ['30', '31'])).
% 3.70/3.89  thf('33', plain, ((r1_tarski @ sk_B @ sk_C)),
% 3.70/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.89  thf(t12_xboole_1, axiom,
% 3.70/3.89    (![A:$i,B:$i]:
% 3.70/3.89     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 3.70/3.89  thf('34', plain,
% 3.70/3.89      (![X6 : $i, X7 : $i]:
% 3.70/3.89         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 3.70/3.89      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.70/3.89  thf('35', plain, (((k2_xboole_0 @ sk_B @ sk_C) = (sk_C))),
% 3.70/3.89      inference('sup-', [status(thm)], ['33', '34'])).
% 3.70/3.89  thf('36', plain,
% 3.70/3.89      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.70/3.89         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 3.70/3.89      inference('cnf', [status(esa)], [t11_xboole_1])).
% 3.70/3.89  thf('37', plain,
% 3.70/3.89      (![X0 : $i]: (~ (r1_tarski @ sk_C @ X0) | (r1_tarski @ sk_B @ X0))),
% 3.70/3.89      inference('sup-', [status(thm)], ['35', '36'])).
% 3.70/3.89  thf('38', plain,
% 3.70/3.89      (![X0 : $i]: (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_C @ X0))),
% 3.70/3.89      inference('sup-', [status(thm)], ['32', '37'])).
% 3.70/3.89  thf('39', plain,
% 3.70/3.89      (![X6 : $i, X7 : $i]:
% 3.70/3.89         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 3.70/3.89      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.70/3.89  thf('40', plain,
% 3.70/3.89      (![X0 : $i]:
% 3.70/3.89         ((k2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0))
% 3.70/3.89           = (k2_xboole_0 @ sk_C @ X0))),
% 3.70/3.89      inference('sup-', [status(thm)], ['38', '39'])).
% 3.70/3.89  thf('41', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 3.70/3.89      inference('sup-', [status(thm)], ['30', '31'])).
% 3.70/3.89  thf('42', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i]:
% 3.70/3.89         (~ (r1_tarski @ X0 @ X1)
% 3.70/3.89          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 3.70/3.89      inference('demod', [status(thm)], ['10', '11'])).
% 3.70/3.89  thf('43', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i]:
% 3.70/3.89         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 3.70/3.89           = (k6_relat_1 @ X1))),
% 3.70/3.89      inference('sup-', [status(thm)], ['41', '42'])).
% 3.70/3.89  thf(t148_relat_1, axiom,
% 3.70/3.89    (![A:$i,B:$i]:
% 3.70/3.89     ( ( v1_relat_1 @ B ) =>
% 3.70/3.89       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 3.70/3.89  thf('44', plain,
% 3.70/3.89      (![X17 : $i, X18 : $i]:
% 3.70/3.89         (((k2_relat_1 @ (k7_relat_1 @ X17 @ X18)) = (k9_relat_1 @ X17 @ X18))
% 3.70/3.89          | ~ (v1_relat_1 @ X17))),
% 3.70/3.89      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.70/3.89  thf('45', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i]:
% 3.70/3.89         (((k2_relat_1 @ (k6_relat_1 @ X0))
% 3.70/3.89            = (k9_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X0 @ X1)))
% 3.70/3.89          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 3.70/3.89      inference('sup+', [status(thm)], ['43', '44'])).
% 3.70/3.89  thf('46', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 3.70/3.89      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.70/3.89  thf('47', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 3.70/3.89      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.70/3.89  thf('48', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i]:
% 3.70/3.89         ((X0) = (k9_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 3.70/3.89      inference('demod', [status(thm)], ['45', '46', '47'])).
% 3.70/3.89  thf('49', plain,
% 3.70/3.89      (![X0 : $i]:
% 3.70/3.89         ((sk_B)
% 3.70/3.89           = (k9_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_xboole_0 @ sk_C @ X0)))),
% 3.70/3.89      inference('sup+', [status(thm)], ['40', '48'])).
% 3.70/3.89  thf(t159_relat_1, axiom,
% 3.70/3.89    (![A:$i,B:$i]:
% 3.70/3.89     ( ( v1_relat_1 @ B ) =>
% 3.70/3.89       ( ![C:$i]:
% 3.70/3.89         ( ( v1_relat_1 @ C ) =>
% 3.70/3.89           ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 3.70/3.89             ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) ))).
% 3.70/3.89  thf('50', plain,
% 3.70/3.89      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.70/3.89         (~ (v1_relat_1 @ X22)
% 3.70/3.89          | ((k9_relat_1 @ (k5_relat_1 @ X23 @ X22) @ X24)
% 3.70/3.89              = (k9_relat_1 @ X22 @ (k9_relat_1 @ X23 @ X24)))
% 3.70/3.89          | ~ (v1_relat_1 @ X23))),
% 3.70/3.89      inference('cnf', [status(esa)], [t159_relat_1])).
% 3.70/3.89  thf('51', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i]:
% 3.70/3.89         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X1) @ 
% 3.70/3.89            (k2_xboole_0 @ sk_C @ X0)) = (k9_relat_1 @ X1 @ sk_B))
% 3.70/3.89          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 3.70/3.89          | ~ (v1_relat_1 @ X1))),
% 3.70/3.89      inference('sup+', [status(thm)], ['49', '50'])).
% 3.70/3.89  thf('52', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 3.70/3.89      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.70/3.89  thf('53', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i]:
% 3.70/3.89         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X1) @ 
% 3.70/3.89            (k2_xboole_0 @ sk_C @ X0)) = (k9_relat_1 @ X1 @ sk_B))
% 3.70/3.89          | ~ (v1_relat_1 @ X1))),
% 3.70/3.89      inference('demod', [status(thm)], ['51', '52'])).
% 3.70/3.89  thf('54', plain,
% 3.70/3.89      (![X27 : $i, X28 : $i]:
% 3.70/3.89         ((r1_tarski @ (k5_relat_1 @ X27 @ (k6_relat_1 @ X28)) @ X27)
% 3.70/3.89          | ~ (v1_relat_1 @ X27))),
% 3.70/3.89      inference('cnf', [status(esa)], [t76_relat_1])).
% 3.70/3.89  thf('55', plain,
% 3.70/3.89      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.70/3.89         (~ (v1_relat_1 @ X19)
% 3.70/3.89          | (r1_tarski @ (k9_relat_1 @ X20 @ X21) @ (k9_relat_1 @ X19 @ X21))
% 3.70/3.89          | ~ (r1_tarski @ X20 @ X19)
% 3.70/3.89          | ~ (v1_relat_1 @ X20))),
% 3.70/3.89      inference('cnf', [status(esa)], [t157_relat_1])).
% 3.70/3.89  thf('56', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.70/3.89         (~ (v1_relat_1 @ X0)
% 3.70/3.89          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 3.70/3.89          | (r1_tarski @ 
% 3.70/3.89             (k9_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X2) @ 
% 3.70/3.89             (k9_relat_1 @ X0 @ X2))
% 3.70/3.89          | ~ (v1_relat_1 @ X0))),
% 3.70/3.89      inference('sup-', [status(thm)], ['54', '55'])).
% 3.70/3.89  thf('57', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.70/3.89         ((r1_tarski @ 
% 3.70/3.89           (k9_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X2) @ 
% 3.70/3.89           (k9_relat_1 @ X0 @ X2))
% 3.70/3.89          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 3.70/3.89          | ~ (v1_relat_1 @ X0))),
% 3.70/3.89      inference('simplify', [status(thm)], ['56'])).
% 3.70/3.89  thf('58', plain,
% 3.70/3.89      (![X27 : $i, X28 : $i]:
% 3.70/3.89         ((r1_tarski @ (k5_relat_1 @ X27 @ (k6_relat_1 @ X28)) @ X27)
% 3.70/3.89          | ~ (v1_relat_1 @ X27))),
% 3.70/3.89      inference('cnf', [status(esa)], [t76_relat_1])).
% 3.70/3.89  thf('59', plain,
% 3.70/3.89      (![X6 : $i, X7 : $i]:
% 3.70/3.89         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 3.70/3.89      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.70/3.89  thf('60', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i]:
% 3.70/3.89         (~ (v1_relat_1 @ X0)
% 3.70/3.89          | ((k2_xboole_0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X0) = (X0)))),
% 3.70/3.89      inference('sup-', [status(thm)], ['58', '59'])).
% 3.70/3.89  thf('61', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 3.70/3.89      inference('sup-', [status(thm)], ['30', '31'])).
% 3.70/3.89  thf(t3_subset, axiom,
% 3.70/3.89    (![A:$i,B:$i]:
% 3.70/3.89     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.70/3.89  thf('62', plain,
% 3.70/3.89      (![X8 : $i, X10 : $i]:
% 3.70/3.89         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 3.70/3.89      inference('cnf', [status(esa)], [t3_subset])).
% 3.70/3.89  thf('63', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i]:
% 3.70/3.89         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.70/3.89      inference('sup-', [status(thm)], ['61', '62'])).
% 3.70/3.89  thf(cc2_relat_1, axiom,
% 3.70/3.89    (![A:$i]:
% 3.70/3.89     ( ( v1_relat_1 @ A ) =>
% 3.70/3.89       ( ![B:$i]:
% 3.70/3.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.70/3.89  thf('64', plain,
% 3.70/3.89      (![X11 : $i, X12 : $i]:
% 3.70/3.89         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 3.70/3.89          | (v1_relat_1 @ X11)
% 3.70/3.89          | ~ (v1_relat_1 @ X12))),
% 3.70/3.89      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.70/3.89  thf('65', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i]:
% 3.70/3.89         (~ (v1_relat_1 @ (k2_xboole_0 @ X1 @ X0)) | (v1_relat_1 @ X1))),
% 3.70/3.89      inference('sup-', [status(thm)], ['63', '64'])).
% 3.70/3.89  thf('66', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i]:
% 3.70/3.89         (~ (v1_relat_1 @ X0)
% 3.70/3.89          | ~ (v1_relat_1 @ X0)
% 3.70/3.89          | (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 3.70/3.89      inference('sup-', [status(thm)], ['60', '65'])).
% 3.70/3.89  thf('67', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i]:
% 3.70/3.89         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 3.70/3.89          | ~ (v1_relat_1 @ X0))),
% 3.70/3.89      inference('simplify', [status(thm)], ['66'])).
% 3.70/3.89  thf('68', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.70/3.89         (~ (v1_relat_1 @ X0)
% 3.70/3.89          | (r1_tarski @ 
% 3.70/3.89             (k9_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X2) @ 
% 3.70/3.89             (k9_relat_1 @ X0 @ X2)))),
% 3.70/3.89      inference('clc', [status(thm)], ['57', '67'])).
% 3.70/3.89  thf('69', plain,
% 3.70/3.89      (![X0 : $i, X1 : $i]:
% 3.70/3.89         ((r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ sk_B) @ 
% 3.70/3.89           (k9_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_xboole_0 @ sk_C @ X1)))
% 3.70/3.89          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.70/3.89          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 3.70/3.89      inference('sup+', [status(thm)], ['53', '68'])).
% 3.70/3.89  thf('70', plain,
% 3.70/3.89      (![X0 : $i]:
% 3.70/3.89         ((sk_B)
% 3.70/3.89           = (k9_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_xboole_0 @ sk_C @ X0)))),
% 3.70/3.89      inference('sup+', [status(thm)], ['40', '48'])).
% 3.70/3.89  thf('71', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 3.70/3.89      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.70/3.89  thf('72', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 3.70/3.89      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.70/3.89  thf('73', plain,
% 3.70/3.89      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ sk_B) @ sk_B)),
% 3.70/3.89      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 3.70/3.89  thf('74', plain, (((k9_relat_1 @ (k6_relat_1 @ sk_C) @ sk_B) = (sk_B))),
% 3.70/3.89      inference('demod', [status(thm)], ['28', '73'])).
% 3.70/3.89  thf('75', plain,
% 3.70/3.89      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.70/3.89         (~ (v1_relat_1 @ X22)
% 3.70/3.89          | ((k9_relat_1 @ (k5_relat_1 @ X23 @ X22) @ X24)
% 3.70/3.89              = (k9_relat_1 @ X22 @ (k9_relat_1 @ X23 @ X24)))
% 3.70/3.89          | ~ (v1_relat_1 @ X23))),
% 3.70/3.89      inference('cnf', [status(esa)], [t159_relat_1])).
% 3.70/3.89  thf('76', plain,
% 3.70/3.89      (![X0 : $i]:
% 3.70/3.89         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ X0) @ sk_B)
% 3.70/3.89            = (k9_relat_1 @ X0 @ sk_B))
% 3.70/3.89          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 3.70/3.89          | ~ (v1_relat_1 @ X0))),
% 3.70/3.89      inference('sup+', [status(thm)], ['74', '75'])).
% 3.70/3.89  thf('77', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 3.70/3.89      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 3.70/3.89  thf('78', plain,
% 3.70/3.89      (![X0 : $i]:
% 3.70/3.89         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ X0) @ sk_B)
% 3.70/3.89            = (k9_relat_1 @ X0 @ sk_B))
% 3.70/3.89          | ~ (v1_relat_1 @ X0))),
% 3.70/3.89      inference('demod', [status(thm)], ['76', '77'])).
% 3.70/3.89  thf('79', plain,
% 3.70/3.89      (![X0 : $i]:
% 3.70/3.89         (((k9_relat_1 @ (k7_relat_1 @ X0 @ sk_C) @ sk_B)
% 3.70/3.89            = (k9_relat_1 @ X0 @ sk_B))
% 3.70/3.89          | ~ (v1_relat_1 @ X0)
% 3.70/3.89          | ~ (v1_relat_1 @ X0))),
% 3.70/3.89      inference('sup+', [status(thm)], ['0', '78'])).
% 3.70/3.89  thf('80', plain,
% 3.70/3.89      (![X0 : $i]:
% 3.70/3.89         (~ (v1_relat_1 @ X0)
% 3.70/3.89          | ((k9_relat_1 @ (k7_relat_1 @ X0 @ sk_C) @ sk_B)
% 3.70/3.89              = (k9_relat_1 @ X0 @ sk_B)))),
% 3.70/3.89      inference('simplify', [status(thm)], ['79'])).
% 3.70/3.89  thf('81', plain,
% 3.70/3.89      (((k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B)
% 3.70/3.89         != (k9_relat_1 @ sk_A @ sk_B))),
% 3.70/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.89  thf('82', plain,
% 3.70/3.89      ((((k9_relat_1 @ sk_A @ sk_B) != (k9_relat_1 @ sk_A @ sk_B))
% 3.70/3.89        | ~ (v1_relat_1 @ sk_A))),
% 3.70/3.89      inference('sup-', [status(thm)], ['80', '81'])).
% 3.70/3.89  thf('83', plain, ((v1_relat_1 @ sk_A)),
% 3.70/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.89  thf('84', plain,
% 3.70/3.89      (((k9_relat_1 @ sk_A @ sk_B) != (k9_relat_1 @ sk_A @ sk_B))),
% 3.70/3.89      inference('demod', [status(thm)], ['82', '83'])).
% 3.70/3.89  thf('85', plain, ($false), inference('simplify', [status(thm)], ['84'])).
% 3.70/3.89  
% 3.70/3.89  % SZS output end Refutation
% 3.70/3.89  
% 3.70/3.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

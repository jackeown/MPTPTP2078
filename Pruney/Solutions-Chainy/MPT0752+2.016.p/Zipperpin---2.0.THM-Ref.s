%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lrDQ3Id2Nn

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 236 expanded)
%              Number of leaves         :   32 (  86 expanded)
%              Depth                    :   15
%              Number of atoms          :  514 (1476 expanded)
%              Number of equality atoms :   51 ( 148 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t45_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v5_ordinal1 @ k1_xboole_0 )
        & ( v1_funct_1 @ k1_xboole_0 )
        & ( v5_relat_1 @ k1_xboole_0 @ A )
        & ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t45_ordinal1])).

thf('0',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
   <= ~ ( v5_ordinal1 @ k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t206_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf('2',plain,(
    ! [X13: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t206_relat_1])).

thf('3',plain,
    ( ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A )
   <= ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v5_relat_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf(t137_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X10: $i] :
      ( ( ( k8_relat_1 @ k1_xboole_0 @ X10 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t137_relat_1])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
   <= ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X24
       != ( k6_relat_1 @ X23 ) )
      | ( ( k1_relat_1 @ X24 )
        = X23 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('14',plain,(
    ! [X23: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X23 ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
        = X23 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X22: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('18',plain,(
    ! [X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X22: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,(
    ~ ( v5_ordinal1 @ k1_xboole_0 ) ),
    inference('sat_resolution*',[status(thm)],['4','12','26','27'])).

thf('29',plain,(
    ~ ( v5_ordinal1 @ k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['1','28'])).

thf(rc3_ordinal1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v5_ordinal1 @ B )
      & ( v1_funct_1 @ B )
      & ( v5_relat_1 @ B @ A )
      & ( v1_relat_1 @ B ) ) )).

thf('30',plain,(
    ! [X26: $i] :
      ( v5_relat_1 @ ( sk_B @ X26 ) @ X26 ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( sk_B @ X26 ) ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( sk_B @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t149_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('35',plain,(
    ! [X12: $i] :
      ( ( ( k9_relat_1 @ X12 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t149_relat_1])).

thf('36',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X11: $i] :
      ( ( ( k9_relat_1 @ X11 @ ( k1_relat_1 @ X11 ) )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['21'])).

thf('43',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['21'])).

thf('44',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','9'])).

thf('45',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf(t120_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
          = A ) ) ) )).

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X6 @ ( k2_relat_1 @ X7 ) )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X6 @ X7 ) )
        = X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t120_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X0 @ k1_xboole_0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','9'])).

thf(t62_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf('49',plain,(
    ! [X15: $i] :
      ( ( ( k5_relat_1 @ k1_xboole_0 @ X15 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t62_relat_1])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k8_relat_1 @ X9 @ X8 )
        = ( k5_relat_1 @ X8 @ ( k6_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','9'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(demod,[status(thm)],['47','48','55','56'])).

thf('58',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ ( sk_B @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','57'])).

thf('59',plain,(
    ! [X16: $i] :
      ( ( ( k2_relat_1 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('60',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    | ( ( sk_B @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( sk_B @ X26 ) ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf('62',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( sk_B @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X26: $i] :
      ( v5_ordinal1 @ ( sk_B @ X26 ) ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf('65',plain,(
    v5_ordinal1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['29','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lrDQ3Id2Nn
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:06:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 61 iterations in 0.027s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(t45_ordinal1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.20/0.49       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.20/0.49          ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t45_ordinal1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((~ (v5_ordinal1 @ k1_xboole_0)
% 0.20/0.49        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.49        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.49        | ~ (v5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      ((~ (v5_ordinal1 @ k1_xboole_0)) <= (~ ((v5_ordinal1 @ k1_xboole_0)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf(t206_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v5_relat_1 @ k1_xboole_0 @ B ) & ( v4_relat_1 @ k1_xboole_0 @ A ) ))).
% 0.20/0.49  thf('2', plain, (![X13 : $i]: (v5_relat_1 @ k1_xboole_0 @ X13)),
% 0.20/0.49      inference('cnf', [status(esa)], [t206_relat_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      ((~ (v5_relat_1 @ k1_xboole_0 @ sk_A))
% 0.20/0.49         <= (~ ((v5_relat_1 @ k1_xboole_0 @ sk_A)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('4', plain, (((v5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.49  thf('5', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.49  thf(t137_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ( k8_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X10 : $i]:
% 0.20/0.49         (((k8_relat_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))
% 0.20/0.49          | ~ (v1_relat_1 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [t137_relat_1])).
% 0.20/0.49  thf(dt_k8_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         ((v1_relat_1 @ (k8_relat_1 @ X3 @ X4)) | ~ (v1_relat_1 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_relat_1 @ k1_xboole_0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.49  thf('10', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ k1_xboole_0)) <= (~ ((v1_relat_1 @ k1_xboole_0)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('12', plain, (((v1_relat_1 @ k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf(t34_funct_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.20/0.49         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X23 : $i, X24 : $i]:
% 0.20/0.49         (((X24) != (k6_relat_1 @ X23))
% 0.20/0.49          | ((k1_relat_1 @ X24) = (X23))
% 0.20/0.49          | ~ (v1_funct_1 @ X24)
% 0.20/0.49          | ~ (v1_relat_1 @ X24))),
% 0.20/0.49      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X23 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k6_relat_1 @ X23))
% 0.20/0.49          | ~ (v1_funct_1 @ (k6_relat_1 @ X23))
% 0.20/0.49          | ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.49  thf('15', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.49  thf(fc3_funct_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.49  thf('16', plain, (![X22 : $i]: (v1_funct_1 @ (k6_relat_1 @ X22))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.49  thf('17', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.49  thf(t64_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.49           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.49         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X16 : $i]:
% 0.20/0.49         (((k1_relat_1 @ X16) != (k1_xboole_0))
% 0.20/0.49          | ((X16) = (k1_xboole_0))
% 0.20/0.49          | ~ (v1_relat_1 @ X16))),
% 0.20/0.49      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((X0) != (k1_xboole_0))
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.49          | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('20', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((X0) != (k1_xboole_0)) | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.49  thf('23', plain, (![X22 : $i]: (v1_funct_1 @ (k6_relat_1 @ X22))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.49  thf('24', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.20/0.49      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      ((~ (v1_funct_1 @ k1_xboole_0)) <= (~ ((v1_funct_1 @ k1_xboole_0)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('26', plain, (((v1_funct_1 @ k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (~ ((v5_ordinal1 @ k1_xboole_0)) | ~ ((v1_funct_1 @ k1_xboole_0)) | 
% 0.20/0.49       ~ ((v1_relat_1 @ k1_xboole_0)) | ~ ((v5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('28', plain, (~ ((v5_ordinal1 @ k1_xboole_0))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['4', '12', '26', '27'])).
% 0.20/0.49  thf('29', plain, (~ (v5_ordinal1 @ k1_xboole_0)),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['1', '28'])).
% 0.20/0.49  thf(rc3_ordinal1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ?[B:$i]:
% 0.20/0.49       ( ( v5_ordinal1 @ B ) & ( v1_funct_1 @ B ) & ( v5_relat_1 @ B @ A ) & 
% 0.20/0.49         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.49  thf('30', plain, (![X26 : $i]: (v5_relat_1 @ (sk_B @ X26) @ X26)),
% 0.20/0.49      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.20/0.49  thf(d19_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v5_relat_1 @ X0 @ X1)
% 0.20/0.49          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (sk_B @ X0))
% 0.20/0.49          | (r1_tarski @ (k2_relat_1 @ (sk_B @ X0)) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.49  thf('33', plain, (![X26 : $i]: (v1_relat_1 @ (sk_B @ X26))),
% 0.20/0.49      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.20/0.49  thf('34', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (sk_B @ X0)) @ X0)),
% 0.20/0.49      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.49  thf(t149_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X12 : $i]:
% 0.20/0.49         (((k9_relat_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.49          | ~ (v1_relat_1 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [t149_relat_1])).
% 0.20/0.49  thf('36', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.49  thf(t146_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X11 : $i]:
% 0.20/0.49         (((k9_relat_1 @ X11 @ (k1_relat_1 @ X11)) = (k2_relat_1 @ X11))
% 0.20/0.49          | ~ (v1_relat_1 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k9_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.20/0.49            = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['36', '37'])).
% 0.20/0.49  thf('39', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.20/0.49           = (k2_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      ((((k1_xboole_0) = (k2_relat_1 @ (k6_relat_1 @ k1_xboole_0)))
% 0.20/0.49        | ~ (v1_relat_1 @ (k6_relat_1 @ k1_xboole_0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['35', '40'])).
% 0.20/0.49  thf('42', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.49  thf('43', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.49  thf('44', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '9'])).
% 0.20/0.49  thf('45', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.20/0.49  thf(t120_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.20/0.49         ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) = ( A ) ) ) ))).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X6 @ (k2_relat_1 @ X7))
% 0.20/0.49          | ((k2_relat_1 @ (k8_relat_1 @ X6 @ X7)) = (X6))
% 0.20/0.49          | ~ (v1_relat_1 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [t120_relat_1])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.20/0.49          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.49          | ((k2_relat_1 @ (k8_relat_1 @ X0 @ k1_xboole_0)) = (X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf('48', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '9'])).
% 0.20/0.49  thf(t62_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.20/0.49         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (![X15 : $i]:
% 0.20/0.49         (((k5_relat_1 @ k1_xboole_0 @ X15) = (k1_xboole_0))
% 0.20/0.49          | ~ (v1_relat_1 @ X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [t62_relat_1])).
% 0.20/0.49  thf(t123_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         (((k8_relat_1 @ X9 @ X8) = (k5_relat_1 @ X8 @ (k6_relat_1 @ X9)))
% 0.20/0.49          | ~ (v1_relat_1 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k8_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['49', '50'])).
% 0.20/0.49  thf('52', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k8_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.49          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.49  thf('54', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '9'])).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      (![X0 : $i]: ((k8_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.49  thf('56', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((k1_xboole_0) = (X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['47', '48', '55', '56'])).
% 0.20/0.49  thf('58', plain, (((k1_xboole_0) = (k2_relat_1 @ (sk_B @ k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['34', '57'])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      (![X16 : $i]:
% 0.20/0.49         (((k2_relat_1 @ X16) != (k1_xboole_0))
% 0.20/0.49          | ((X16) = (k1_xboole_0))
% 0.20/0.49          | ~ (v1_relat_1 @ X16))),
% 0.20/0.49      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49        | ~ (v1_relat_1 @ (sk_B @ k1_xboole_0))
% 0.20/0.49        | ((sk_B @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.49  thf('61', plain, (![X26 : $i]: (v1_relat_1 @ (sk_B @ X26))),
% 0.20/0.49      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.20/0.49  thf('62', plain,
% 0.20/0.49      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49        | ((sk_B @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.49  thf('63', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['62'])).
% 0.20/0.49  thf('64', plain, (![X26 : $i]: (v5_ordinal1 @ (sk_B @ X26))),
% 0.20/0.49      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.20/0.49  thf('65', plain, ((v5_ordinal1 @ k1_xboole_0)),
% 0.20/0.49      inference('sup+', [status(thm)], ['63', '64'])).
% 0.20/0.49  thf('66', plain, ($false), inference('demod', [status(thm)], ['29', '65'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

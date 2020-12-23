%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wVs9FGKP49

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:23 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 454 expanded)
%              Number of leaves         :   31 ( 159 expanded)
%              Depth                    :   23
%              Number of atoms          : 1149 (3854 expanded)
%              Number of equality atoms :   81 ( 217 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t146_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X47 @ X46 ) @ X48 )
        = ( k3_xboole_0 @ X46 @ ( k10_relat_1 @ X47 @ X48 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X37: $i] :
      ( ( ( k10_relat_1 @ X37 @ ( k2_relat_1 @ X37 ) )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('7',plain,(
    ! [X42: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ( v4_relat_1 @ X28 @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( v4_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v4_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    v4_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40
        = ( k7_relat_1 @ X40 @ X41 ) )
      | ~ ( v4_relat_1 @ X40 @ X41 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ( ( k6_relat_1 @ sk_A )
      = ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('16',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t189_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) )
            = ( k7_relat_1 @ A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( ( k7_relat_1 @ X39 @ ( k1_relat_1 @ X38 ) )
        = ( k7_relat_1 @ X39 @ ( k1_relat_1 @ ( k7_relat_1 @ X38 @ ( k1_relat_1 @ X39 ) ) ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('18',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( ( k7_relat_1 @ X39 @ ( k1_relat_1 @ X38 ) )
        = ( k7_relat_1 @ X39 @ ( k1_relat_1 @ ( k7_relat_1 @ X38 @ ( k1_relat_1 @ X39 ) ) ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ sk_B ) )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('23',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('24',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('25',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('26',plain,(
    ! [X42: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('29',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25','26','27','28'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('30',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X44 @ X45 ) ) @ X45 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('31',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X42: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('33',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('34',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X44 @ X45 ) ) @ X45 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X47 @ X46 ) @ X48 )
        = ( k3_xboole_0 @ X46 @ ( k10_relat_1 @ X47 @ X48 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('42',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ( v4_relat_1 @ X28 @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40
        = ( k7_relat_1 @ X40 @ X41 ) )
      | ~ ( v4_relat_1 @ X40 @ X41 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X47 @ X46 ) @ X48 )
        = ( k3_xboole_0 @ X46 @ ( k10_relat_1 @ X47 @ X48 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ X1 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['41','51'])).

thf('53',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 )
        = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['40','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('59',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( ( k7_relat_1 @ X39 @ ( k1_relat_1 @ X38 ) )
        = ( k7_relat_1 @ X39 @ ( k1_relat_1 @ ( k7_relat_1 @ X38 @ ( k1_relat_1 @ X39 ) ) ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('60',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X47 @ X46 ) @ X48 )
        = ( k3_xboole_0 @ X46 @ ( k10_relat_1 @ X47 @ X48 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) @ ( k10_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) @ ( k10_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) @ X0 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) @ ( k10_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['58','62'])).

thf('64',plain,(
    ! [X42: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('65',plain,(
    ! [X42: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['57','68'])).

thf('70',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
      = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['5','69'])).

thf('71',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('73',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('75',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('76',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['42'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('78',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('81',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','82'])).

thf('84',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['76','83'])).

thf('85',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('86',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('89',plain,(
    ! [X33: $i] :
      ( ( ( k9_relat_1 @ X33 @ ( k1_relat_1 @ X33 ) )
        = ( k2_relat_1 @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('90',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X44 @ X45 ) ) @ X45 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('91',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ X34 @ X35 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X36 @ X35 ) @ X34 )
        = ( k9_relat_1 @ X36 @ X34 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = ( k9_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['88','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','99'])).

thf('101',plain,(
    $false ),
    inference(demod,[status(thm)],['0','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wVs9FGKP49
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:10:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.75/1.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/1.01  % Solved by: fo/fo7.sh
% 0.75/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/1.01  % done 950 iterations in 0.555s
% 0.75/1.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/1.01  % SZS output start Refutation
% 0.75/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/1.01  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/1.01  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.75/1.01  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/1.01  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/1.01  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.75/1.01  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.75/1.01  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/1.01  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.75/1.01  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.75/1.01  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.75/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.75/1.01  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.75/1.01  thf(t146_funct_1, conjecture,
% 0.75/1.01    (![A:$i,B:$i]:
% 0.75/1.01     ( ( v1_relat_1 @ B ) =>
% 0.75/1.01       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.75/1.01         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.75/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.75/1.01    (~( ![A:$i,B:$i]:
% 0.75/1.01        ( ( v1_relat_1 @ B ) =>
% 0.75/1.01          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.75/1.01            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.75/1.01    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.75/1.01  thf('0', plain,
% 0.75/1.01      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf(t139_funct_1, axiom,
% 0.75/1.01    (![A:$i,B:$i,C:$i]:
% 0.75/1.01     ( ( v1_relat_1 @ C ) =>
% 0.75/1.01       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.75/1.01         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.75/1.01  thf('1', plain,
% 0.75/1.01      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.75/1.01         (((k10_relat_1 @ (k7_relat_1 @ X47 @ X46) @ X48)
% 0.75/1.01            = (k3_xboole_0 @ X46 @ (k10_relat_1 @ X47 @ X48)))
% 0.75/1.01          | ~ (v1_relat_1 @ X47))),
% 0.75/1.01      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.75/1.01  thf(t169_relat_1, axiom,
% 0.75/1.01    (![A:$i]:
% 0.75/1.01     ( ( v1_relat_1 @ A ) =>
% 0.75/1.01       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.75/1.01  thf('2', plain,
% 0.75/1.01      (![X37 : $i]:
% 0.75/1.01         (((k10_relat_1 @ X37 @ (k2_relat_1 @ X37)) = (k1_relat_1 @ X37))
% 0.75/1.01          | ~ (v1_relat_1 @ X37))),
% 0.75/1.01      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.75/1.01  thf('3', plain,
% 0.75/1.01      (![X0 : $i, X1 : $i]:
% 0.75/1.01         (((k3_xboole_0 @ X0 @ 
% 0.75/1.01            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.75/1.01            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.75/1.01          | ~ (v1_relat_1 @ X1)
% 0.75/1.01          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.75/1.01      inference('sup+', [status(thm)], ['1', '2'])).
% 0.75/1.01  thf(dt_k7_relat_1, axiom,
% 0.75/1.01    (![A:$i,B:$i]:
% 0.75/1.01     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.75/1.01  thf('4', plain,
% 0.75/1.01      (![X31 : $i, X32 : $i]:
% 0.75/1.01         (~ (v1_relat_1 @ X31) | (v1_relat_1 @ (k7_relat_1 @ X31 @ X32)))),
% 0.75/1.01      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.75/1.01  thf('5', plain,
% 0.75/1.01      (![X0 : $i, X1 : $i]:
% 0.75/1.01         (~ (v1_relat_1 @ X1)
% 0.75/1.01          | ((k3_xboole_0 @ X0 @ 
% 0.75/1.01              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.75/1.01              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.75/1.01      inference('clc', [status(thm)], ['3', '4'])).
% 0.75/1.01  thf('6', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf(t71_relat_1, axiom,
% 0.75/1.01    (![A:$i]:
% 0.75/1.01     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.75/1.01       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.75/1.01  thf('7', plain, (![X42 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X42)) = (X42))),
% 0.75/1.01      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.75/1.01  thf(d18_relat_1, axiom,
% 0.75/1.01    (![A:$i,B:$i]:
% 0.75/1.01     ( ( v1_relat_1 @ B ) =>
% 0.75/1.01       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.75/1.01  thf('8', plain,
% 0.75/1.01      (![X28 : $i, X29 : $i]:
% 0.75/1.01         (~ (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 0.75/1.01          | (v4_relat_1 @ X28 @ X29)
% 0.75/1.01          | ~ (v1_relat_1 @ X28))),
% 0.75/1.01      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.75/1.01  thf('9', plain,
% 0.75/1.01      (![X0 : $i, X1 : $i]:
% 0.75/1.01         (~ (r1_tarski @ X0 @ X1)
% 0.75/1.01          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.75/1.01          | (v4_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.75/1.01      inference('sup-', [status(thm)], ['7', '8'])).
% 0.75/1.01  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.75/1.01  thf('10', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.75/1.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/1.01  thf('11', plain,
% 0.75/1.01      (![X0 : $i, X1 : $i]:
% 0.75/1.01         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.75/1.01      inference('demod', [status(thm)], ['9', '10'])).
% 0.75/1.01  thf('12', plain, ((v4_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 0.75/1.01      inference('sup-', [status(thm)], ['6', '11'])).
% 0.75/1.01  thf(t209_relat_1, axiom,
% 0.75/1.01    (![A:$i,B:$i]:
% 0.75/1.01     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.75/1.01       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.75/1.01  thf('13', plain,
% 0.75/1.01      (![X40 : $i, X41 : $i]:
% 0.75/1.01         (((X40) = (k7_relat_1 @ X40 @ X41))
% 0.75/1.01          | ~ (v4_relat_1 @ X40 @ X41)
% 0.75/1.01          | ~ (v1_relat_1 @ X40))),
% 0.75/1.01      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.75/1.01  thf('14', plain,
% 0.75/1.01      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.75/1.01        | ((k6_relat_1 @ sk_A)
% 0.75/1.01            = (k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 0.75/1.01      inference('sup-', [status(thm)], ['12', '13'])).
% 0.75/1.01  thf('15', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.75/1.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/1.01  thf('16', plain,
% 0.75/1.01      (((k6_relat_1 @ sk_A)
% 0.75/1.01         = (k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.75/1.01      inference('demod', [status(thm)], ['14', '15'])).
% 0.75/1.01  thf(t189_relat_1, axiom,
% 0.75/1.01    (![A:$i]:
% 0.75/1.01     ( ( v1_relat_1 @ A ) =>
% 0.75/1.01       ( ![B:$i]:
% 0.75/1.01         ( ( v1_relat_1 @ B ) =>
% 0.75/1.01           ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) ) =
% 0.75/1.01             ( k7_relat_1 @
% 0.75/1.01               A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ))).
% 0.75/1.01  thf('17', plain,
% 0.75/1.01      (![X38 : $i, X39 : $i]:
% 0.75/1.01         (~ (v1_relat_1 @ X38)
% 0.75/1.01          | ((k7_relat_1 @ X39 @ (k1_relat_1 @ X38))
% 0.75/1.01              = (k7_relat_1 @ X39 @ 
% 0.75/1.01                 (k1_relat_1 @ (k7_relat_1 @ X38 @ (k1_relat_1 @ X39)))))
% 0.75/1.01          | ~ (v1_relat_1 @ X39))),
% 0.75/1.01      inference('cnf', [status(esa)], [t189_relat_1])).
% 0.75/1.01  thf('18', plain,
% 0.75/1.01      (![X38 : $i, X39 : $i]:
% 0.75/1.01         (~ (v1_relat_1 @ X38)
% 0.75/1.01          | ((k7_relat_1 @ X39 @ (k1_relat_1 @ X38))
% 0.75/1.01              = (k7_relat_1 @ X39 @ 
% 0.75/1.01                 (k1_relat_1 @ (k7_relat_1 @ X38 @ (k1_relat_1 @ X39)))))
% 0.75/1.01          | ~ (v1_relat_1 @ X39))),
% 0.75/1.01      inference('cnf', [status(esa)], [t189_relat_1])).
% 0.75/1.01  thf('19', plain,
% 0.75/1.01      (![X0 : $i, X1 : $i]:
% 0.75/1.01         (((k7_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)) @ 
% 0.75/1.01            (k1_relat_1 @ X1))
% 0.75/1.01            = (k7_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)) @ 
% 0.75/1.01               (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))))
% 0.75/1.01          | ~ (v1_relat_1 @ X1)
% 0.75/1.01          | ~ (v1_relat_1 @ X0)
% 0.75/1.01          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))
% 0.75/1.01          | ~ (v1_relat_1 @ X1))),
% 0.75/1.01      inference('sup+', [status(thm)], ['17', '18'])).
% 0.75/1.01  thf('20', plain,
% 0.75/1.01      (![X0 : $i, X1 : $i]:
% 0.75/1.01         (~ (v1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)))
% 0.75/1.01          | ~ (v1_relat_1 @ X0)
% 0.75/1.01          | ~ (v1_relat_1 @ X1)
% 0.75/1.01          | ((k7_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)) @ 
% 0.75/1.01              (k1_relat_1 @ X1))
% 0.75/1.01              = (k7_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1)) @ 
% 0.75/1.01                 (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0))))))),
% 0.75/1.01      inference('simplify', [status(thm)], ['19'])).
% 0.75/1.01  thf('21', plain,
% 0.75/1.01      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.75/1.01        | ((k7_relat_1 @ 
% 0.75/1.01            (k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) @ 
% 0.75/1.01            (k1_relat_1 @ sk_B))
% 0.75/1.01            = (k7_relat_1 @ 
% 0.75/1.01               (k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) @ 
% 0.75/1.01               (k1_relat_1 @ 
% 0.75/1.01                (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k6_relat_1 @ sk_A))))))
% 0.75/1.01        | ~ (v1_relat_1 @ sk_B)
% 0.75/1.01        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.75/1.01      inference('sup-', [status(thm)], ['16', '20'])).
% 0.75/1.01  thf('22', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.75/1.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/1.01  thf('23', plain,
% 0.75/1.01      (((k6_relat_1 @ sk_A)
% 0.75/1.01         = (k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.75/1.01      inference('demod', [status(thm)], ['14', '15'])).
% 0.75/1.01  thf('24', plain,
% 0.75/1.01      (((k6_relat_1 @ sk_A)
% 0.75/1.01         = (k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.75/1.01      inference('demod', [status(thm)], ['14', '15'])).
% 0.75/1.01  thf('25', plain,
% 0.75/1.01      (((k6_relat_1 @ sk_A)
% 0.75/1.01         = (k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.75/1.01      inference('demod', [status(thm)], ['14', '15'])).
% 0.75/1.01  thf('26', plain, (![X42 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X42)) = (X42))),
% 0.75/1.01      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.75/1.01  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('28', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.75/1.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/1.01  thf('29', plain,
% 0.75/1.01      (((k6_relat_1 @ sk_A)
% 0.75/1.01         = (k7_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 0.75/1.01            (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.75/1.01      inference('demod', [status(thm)],
% 0.75/1.01                ['21', '22', '23', '24', '25', '26', '27', '28'])).
% 0.75/1.01  thf(t87_relat_1, axiom,
% 0.75/1.01    (![A:$i,B:$i]:
% 0.75/1.01     ( ( v1_relat_1 @ B ) =>
% 0.75/1.01       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.75/1.01  thf('30', plain,
% 0.75/1.01      (![X44 : $i, X45 : $i]:
% 0.75/1.01         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X44 @ X45)) @ X45)
% 0.75/1.01          | ~ (v1_relat_1 @ X44))),
% 0.75/1.01      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.75/1.01  thf('31', plain,
% 0.75/1.01      (((r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ sk_A)) @ 
% 0.75/1.01         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.75/1.01        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.75/1.01      inference('sup+', [status(thm)], ['29', '30'])).
% 0.75/1.01  thf('32', plain, (![X42 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X42)) = (X42))),
% 0.75/1.01      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.75/1.01  thf('33', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.75/1.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/1.01  thf('34', plain,
% 0.75/1.01      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.75/1.01      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.75/1.01  thf('35', plain,
% 0.75/1.01      (![X44 : $i, X45 : $i]:
% 0.75/1.01         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X44 @ X45)) @ X45)
% 0.75/1.01          | ~ (v1_relat_1 @ X44))),
% 0.75/1.01      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.75/1.01  thf(d10_xboole_0, axiom,
% 0.75/1.01    (![A:$i,B:$i]:
% 0.75/1.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.75/1.01  thf('36', plain,
% 0.75/1.01      (![X1 : $i, X3 : $i]:
% 0.75/1.01         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.75/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/1.01  thf('37', plain,
% 0.75/1.01      (![X0 : $i, X1 : $i]:
% 0.75/1.01         (~ (v1_relat_1 @ X1)
% 0.75/1.01          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.75/1.01          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.75/1.01      inference('sup-', [status(thm)], ['35', '36'])).
% 0.75/1.01  thf('38', plain,
% 0.75/1.01      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.75/1.01        | ~ (v1_relat_1 @ sk_B))),
% 0.75/1.01      inference('sup-', [status(thm)], ['34', '37'])).
% 0.75/1.01  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('40', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.75/1.01      inference('demod', [status(thm)], ['38', '39'])).
% 0.75/1.01  thf('41', plain,
% 0.75/1.01      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.75/1.01         (((k10_relat_1 @ (k7_relat_1 @ X47 @ X46) @ X48)
% 0.75/1.01            = (k3_xboole_0 @ X46 @ (k10_relat_1 @ X47 @ X48)))
% 0.75/1.01          | ~ (v1_relat_1 @ X47))),
% 0.75/1.01      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.75/1.01  thf('42', plain,
% 0.75/1.01      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.75/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/1.01  thf('43', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.75/1.01      inference('simplify', [status(thm)], ['42'])).
% 0.75/1.01  thf('44', plain,
% 0.75/1.01      (![X28 : $i, X29 : $i]:
% 0.75/1.01         (~ (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 0.75/1.01          | (v4_relat_1 @ X28 @ X29)
% 0.75/1.01          | ~ (v1_relat_1 @ X28))),
% 0.75/1.01      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.75/1.01  thf('45', plain,
% 0.75/1.01      (![X0 : $i]:
% 0.75/1.01         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.75/1.01      inference('sup-', [status(thm)], ['43', '44'])).
% 0.75/1.01  thf('46', plain,
% 0.75/1.01      (![X40 : $i, X41 : $i]:
% 0.75/1.01         (((X40) = (k7_relat_1 @ X40 @ X41))
% 0.75/1.01          | ~ (v4_relat_1 @ X40 @ X41)
% 0.75/1.01          | ~ (v1_relat_1 @ X40))),
% 0.75/1.01      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.75/1.01  thf('47', plain,
% 0.75/1.01      (![X0 : $i]:
% 0.75/1.01         (~ (v1_relat_1 @ X0)
% 0.75/1.01          | ~ (v1_relat_1 @ X0)
% 0.75/1.01          | ((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.75/1.01      inference('sup-', [status(thm)], ['45', '46'])).
% 0.75/1.01  thf('48', plain,
% 0.75/1.01      (![X0 : $i]:
% 0.75/1.01         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 0.75/1.01      inference('simplify', [status(thm)], ['47'])).
% 0.75/1.01  thf('49', plain,
% 0.75/1.01      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.75/1.01         (((k10_relat_1 @ (k7_relat_1 @ X47 @ X46) @ X48)
% 0.75/1.01            = (k3_xboole_0 @ X46 @ (k10_relat_1 @ X47 @ X48)))
% 0.75/1.01          | ~ (v1_relat_1 @ X47))),
% 0.75/1.01      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.75/1.01  thf('50', plain,
% 0.75/1.01      (![X0 : $i, X1 : $i]:
% 0.75/1.01         (((k10_relat_1 @ X0 @ X1)
% 0.75/1.01            = (k3_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1)))
% 0.75/1.01          | ~ (v1_relat_1 @ X0)
% 0.75/1.01          | ~ (v1_relat_1 @ X0))),
% 0.75/1.01      inference('sup+', [status(thm)], ['48', '49'])).
% 0.75/1.01  thf('51', plain,
% 0.75/1.01      (![X0 : $i, X1 : $i]:
% 0.75/1.01         (~ (v1_relat_1 @ X0)
% 0.75/1.01          | ((k10_relat_1 @ X0 @ X1)
% 0.75/1.01              = (k3_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))))),
% 0.75/1.01      inference('simplify', [status(thm)], ['50'])).
% 0.75/1.01  thf('52', plain,
% 0.75/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/1.01         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)
% 0.75/1.01            = (k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)) @ 
% 0.75/1.01               (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))))
% 0.75/1.01          | ~ (v1_relat_1 @ X1)
% 0.75/1.01          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 0.75/1.01      inference('sup+', [status(thm)], ['41', '51'])).
% 0.75/1.01  thf('53', plain,
% 0.75/1.01      (![X31 : $i, X32 : $i]:
% 0.75/1.01         (~ (v1_relat_1 @ X31) | (v1_relat_1 @ (k7_relat_1 @ X31 @ X32)))),
% 0.75/1.01      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.75/1.01  thf('54', plain,
% 0.75/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/1.01         (~ (v1_relat_1 @ X1)
% 0.75/1.01          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)
% 0.75/1.01              = (k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)) @ 
% 0.75/1.01                 (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))))),
% 0.75/1.01      inference('clc', [status(thm)], ['52', '53'])).
% 0.75/1.01  thf('55', plain,
% 0.75/1.01      (![X0 : $i]:
% 0.75/1.01         (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)
% 0.75/1.01            = (k3_xboole_0 @ sk_A @ 
% 0.75/1.01               (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0))))
% 0.75/1.01          | ~ (v1_relat_1 @ sk_B))),
% 0.75/1.01      inference('sup+', [status(thm)], ['40', '54'])).
% 0.75/1.01  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('57', plain,
% 0.75/1.01      (![X0 : $i]:
% 0.75/1.01         ((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)
% 0.75/1.01           = (k3_xboole_0 @ sk_A @ 
% 0.75/1.01              (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0))))),
% 0.75/1.01      inference('demod', [status(thm)], ['55', '56'])).
% 0.75/1.01  thf('58', plain,
% 0.75/1.01      (((k6_relat_1 @ sk_A)
% 0.75/1.01         = (k7_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.75/1.01      inference('demod', [status(thm)], ['14', '15'])).
% 0.75/1.01  thf('59', plain,
% 0.75/1.01      (![X38 : $i, X39 : $i]:
% 0.75/1.01         (~ (v1_relat_1 @ X38)
% 0.75/1.01          | ((k7_relat_1 @ X39 @ (k1_relat_1 @ X38))
% 0.75/1.01              = (k7_relat_1 @ X39 @ 
% 0.75/1.01                 (k1_relat_1 @ (k7_relat_1 @ X38 @ (k1_relat_1 @ X39)))))
% 0.75/1.01          | ~ (v1_relat_1 @ X39))),
% 0.75/1.01      inference('cnf', [status(esa)], [t189_relat_1])).
% 0.75/1.01  thf('60', plain,
% 0.75/1.01      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.75/1.01         (((k10_relat_1 @ (k7_relat_1 @ X47 @ X46) @ X48)
% 0.75/1.01            = (k3_xboole_0 @ X46 @ (k10_relat_1 @ X47 @ X48)))
% 0.75/1.01          | ~ (v1_relat_1 @ X47))),
% 0.75/1.01      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.75/1.01  thf('61', plain,
% 0.75/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/1.01         (((k10_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ X2)
% 0.75/1.01            = (k3_xboole_0 @ 
% 0.75/1.01               (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1))) @ 
% 0.75/1.01               (k10_relat_1 @ X1 @ X2)))
% 0.75/1.01          | ~ (v1_relat_1 @ X1)
% 0.75/1.01          | ~ (v1_relat_1 @ X0)
% 0.75/1.01          | ~ (v1_relat_1 @ X1))),
% 0.75/1.01      inference('sup+', [status(thm)], ['59', '60'])).
% 0.75/1.01  thf('62', plain,
% 0.75/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/1.01         (~ (v1_relat_1 @ X0)
% 0.75/1.01          | ~ (v1_relat_1 @ X1)
% 0.75/1.01          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ X2)
% 0.75/1.01              = (k3_xboole_0 @ 
% 0.75/1.01                 (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X1))) @ 
% 0.75/1.01                 (k10_relat_1 @ X1 @ X2))))),
% 0.75/1.01      inference('simplify', [status(thm)], ['61'])).
% 0.75/1.01  thf('63', plain,
% 0.75/1.01      (![X0 : $i]:
% 0.75/1.01         (((k10_relat_1 @ 
% 0.75/1.01            (k7_relat_1 @ sk_B @ (k1_relat_1 @ (k6_relat_1 @ sk_A))) @ X0)
% 0.75/1.01            = (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ sk_A)) @ 
% 0.75/1.01               (k10_relat_1 @ sk_B @ X0)))
% 0.75/1.01          | ~ (v1_relat_1 @ sk_B)
% 0.75/1.01          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.75/1.01      inference('sup+', [status(thm)], ['58', '62'])).
% 0.75/1.01  thf('64', plain, (![X42 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X42)) = (X42))),
% 0.75/1.01      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.75/1.01  thf('65', plain, (![X42 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X42)) = (X42))),
% 0.75/1.01      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.75/1.01  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('67', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.75/1.01      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.75/1.01  thf('68', plain,
% 0.75/1.01      (![X0 : $i]:
% 0.75/1.01         ((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)
% 0.75/1.01           = (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0)))),
% 0.75/1.01      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.75/1.01  thf('69', plain,
% 0.75/1.01      (![X0 : $i]:
% 0.75/1.01         ((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0))
% 0.75/1.01           = (k3_xboole_0 @ sk_A @ 
% 0.75/1.01              (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0))))),
% 0.75/1.01      inference('demod', [status(thm)], ['57', '68'])).
% 0.75/1.01  thf('70', plain,
% 0.75/1.01      ((((k3_xboole_0 @ sk_A @ 
% 0.75/1.01          (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.75/1.01          = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.75/1.01        | ~ (v1_relat_1 @ sk_B))),
% 0.75/1.01      inference('sup+', [status(thm)], ['5', '69'])).
% 0.75/1.01  thf('71', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.75/1.01      inference('demod', [status(thm)], ['38', '39'])).
% 0.75/1.01  thf(idempotence_k3_xboole_0, axiom,
% 0.75/1.01    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.75/1.01  thf('72', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.75/1.01      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.75/1.01  thf('73', plain, ((v1_relat_1 @ sk_B)),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('74', plain,
% 0.75/1.01      (((k3_xboole_0 @ sk_A @ 
% 0.75/1.01         (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.75/1.01         = (sk_A))),
% 0.75/1.01      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.75/1.01  thf(t100_xboole_1, axiom,
% 0.75/1.01    (![A:$i,B:$i]:
% 0.75/1.01     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.75/1.01  thf('75', plain,
% 0.75/1.01      (![X7 : $i, X8 : $i]:
% 0.75/1.01         ((k4_xboole_0 @ X7 @ X8)
% 0.75/1.01           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.75/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/1.01  thf('76', plain,
% 0.75/1.01      (((k4_xboole_0 @ sk_A @ 
% 0.75/1.01         (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.75/1.01         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.75/1.01      inference('sup+', [status(thm)], ['74', '75'])).
% 0.75/1.01  thf('77', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.75/1.01      inference('simplify', [status(thm)], ['42'])).
% 0.75/1.01  thf(l32_xboole_1, axiom,
% 0.75/1.01    (![A:$i,B:$i]:
% 0.75/1.01     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.75/1.01  thf('78', plain,
% 0.75/1.01      (![X4 : $i, X6 : $i]:
% 0.75/1.01         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.75/1.01      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.75/1.01  thf('79', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.75/1.01      inference('sup-', [status(thm)], ['77', '78'])).
% 0.75/1.01  thf('80', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.75/1.01      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.75/1.01  thf('81', plain,
% 0.75/1.01      (![X7 : $i, X8 : $i]:
% 0.75/1.01         ((k4_xboole_0 @ X7 @ X8)
% 0.75/1.01           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.75/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/1.01  thf('82', plain,
% 0.75/1.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.75/1.01      inference('sup+', [status(thm)], ['80', '81'])).
% 0.75/1.01  thf('83', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.75/1.01      inference('sup+', [status(thm)], ['79', '82'])).
% 0.75/1.01  thf('84', plain,
% 0.75/1.01      (((k4_xboole_0 @ sk_A @ 
% 0.75/1.01         (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.75/1.01         = (k1_xboole_0))),
% 0.75/1.01      inference('demod', [status(thm)], ['76', '83'])).
% 0.75/1.01  thf('85', plain,
% 0.75/1.01      (![X4 : $i, X5 : $i]:
% 0.75/1.01         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.75/1.01      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.75/1.01  thf('86', plain,
% 0.75/1.01      ((((k1_xboole_0) != (k1_xboole_0))
% 0.75/1.01        | (r1_tarski @ sk_A @ 
% 0.75/1.01           (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))))),
% 0.75/1.01      inference('sup-', [status(thm)], ['84', '85'])).
% 0.75/1.01  thf('87', plain,
% 0.75/1.01      ((r1_tarski @ sk_A @ 
% 0.75/1.01        (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.75/1.01      inference('simplify', [status(thm)], ['86'])).
% 0.75/1.01  thf('88', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.75/1.01      inference('demod', [status(thm)], ['38', '39'])).
% 0.75/1.01  thf(t146_relat_1, axiom,
% 0.75/1.01    (![A:$i]:
% 0.75/1.01     ( ( v1_relat_1 @ A ) =>
% 0.75/1.01       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.75/1.01  thf('89', plain,
% 0.75/1.01      (![X33 : $i]:
% 0.75/1.01         (((k9_relat_1 @ X33 @ (k1_relat_1 @ X33)) = (k2_relat_1 @ X33))
% 0.75/1.01          | ~ (v1_relat_1 @ X33))),
% 0.75/1.01      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.75/1.01  thf('90', plain,
% 0.75/1.01      (![X44 : $i, X45 : $i]:
% 0.75/1.01         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X44 @ X45)) @ X45)
% 0.75/1.01          | ~ (v1_relat_1 @ X44))),
% 0.75/1.01      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.75/1.01  thf(t162_relat_1, axiom,
% 0.75/1.01    (![A:$i]:
% 0.75/1.01     ( ( v1_relat_1 @ A ) =>
% 0.75/1.01       ( ![B:$i,C:$i]:
% 0.75/1.01         ( ( r1_tarski @ B @ C ) =>
% 0.75/1.01           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.75/1.01             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.75/1.01  thf('91', plain,
% 0.75/1.01      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.75/1.01         (~ (r1_tarski @ X34 @ X35)
% 0.75/1.01          | ((k9_relat_1 @ (k7_relat_1 @ X36 @ X35) @ X34)
% 0.75/1.01              = (k9_relat_1 @ X36 @ X34))
% 0.75/1.01          | ~ (v1_relat_1 @ X36))),
% 0.75/1.01      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.75/1.01  thf('92', plain,
% 0.75/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/1.01         (~ (v1_relat_1 @ X1)
% 0.75/1.01          | ~ (v1_relat_1 @ X2)
% 0.75/1.01          | ((k9_relat_1 @ (k7_relat_1 @ X2 @ X0) @ 
% 0.75/1.01              (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.75/1.01              = (k9_relat_1 @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))))),
% 0.75/1.01      inference('sup-', [status(thm)], ['90', '91'])).
% 0.75/1.01  thf('93', plain,
% 0.75/1.01      (![X0 : $i, X1 : $i]:
% 0.75/1.01         (((k2_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.75/1.01            = (k9_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.75/1.01          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.75/1.01          | ~ (v1_relat_1 @ X1)
% 0.75/1.01          | ~ (v1_relat_1 @ X1))),
% 0.75/1.01      inference('sup+', [status(thm)], ['89', '92'])).
% 0.75/1.01  thf('94', plain,
% 0.75/1.01      (![X0 : $i, X1 : $i]:
% 0.75/1.01         (~ (v1_relat_1 @ X1)
% 0.75/1.01          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.75/1.01          | ((k2_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.75/1.01              = (k9_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))))),
% 0.75/1.01      inference('simplify', [status(thm)], ['93'])).
% 0.75/1.01  thf('95', plain,
% 0.75/1.01      (![X31 : $i, X32 : $i]:
% 0.75/1.01         (~ (v1_relat_1 @ X31) | (v1_relat_1 @ (k7_relat_1 @ X31 @ X32)))),
% 0.75/1.01      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.75/1.01  thf('96', plain,
% 0.75/1.01      (![X0 : $i, X1 : $i]:
% 0.75/1.01         (((k2_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.75/1.01            = (k9_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.75/1.01          | ~ (v1_relat_1 @ X1))),
% 0.75/1.01      inference('clc', [status(thm)], ['94', '95'])).
% 0.75/1.01  thf('97', plain,
% 0.75/1.01      ((((k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k9_relat_1 @ sk_B @ sk_A))
% 0.75/1.01        | ~ (v1_relat_1 @ sk_B))),
% 0.75/1.01      inference('sup+', [status(thm)], ['88', '96'])).
% 0.75/1.01  thf('98', plain, ((v1_relat_1 @ sk_B)),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('99', plain,
% 0.75/1.01      (((k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k9_relat_1 @ sk_B @ sk_A))),
% 0.75/1.01      inference('demod', [status(thm)], ['97', '98'])).
% 0.75/1.01  thf('100', plain,
% 0.75/1.01      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.75/1.01      inference('demod', [status(thm)], ['87', '99'])).
% 0.75/1.01  thf('101', plain, ($false), inference('demod', [status(thm)], ['0', '100'])).
% 0.75/1.01  
% 0.75/1.01  % SZS output end Refutation
% 0.75/1.01  
% 0.88/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0770+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xVWCt9dcMt

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:28 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  231 (1809 expanded)
%              Number of leaves         :   35 ( 520 expanded)
%              Depth                    :   51
%              Number of atoms          : 1985 (19563 expanded)
%              Number of equality atoms :   49 ( 540 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf(t19_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k3_relat_1 @ ( k2_wellord1 @ C @ B ) ) )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ ( k2_wellord1 @ C @ B ) ) )
         => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
            & ( r2_hidden @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_wellord1])).

thf('1',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( ( ( k3_relat_1 @ X12 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('4',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t18_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf('10',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_wellord1 @ X26 @ X25 )
        = ( k8_relat_1 @ X25 @ ( k7_relat_1 @ X26 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t18_wellord1])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X22 @ X21 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('16',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X2 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t99_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X40 @ X41 ) ) @ ( k2_relat_1 @ X40 ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t99_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X29: $i,X31: $i] :
      ( ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( r1_tarski @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('24',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('31',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( m1_subset_1 @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X2 @ ( k2_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ( m1_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ( m1_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t17_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ) )).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_wellord1 @ X24 @ X23 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X23 @ X24 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('37',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X38 ) @ X39 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(l29_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('46',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X19 @ X20 ) ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l29_wellord1])).

thf('47',plain,(
    ! [X29: $i,X31: $i] :
      ( ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( r1_tarski @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( m1_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( m1_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('56',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( m1_subset_1 @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('61',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X12: $i] :
      ( ( ( k3_relat_1 @ X12 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('64',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['64'])).

thf('70',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['64'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k3_xboole_0 @ ( k3_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','76'])).

thf('78',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) )
   <= ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['83'])).

thf('85',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('86',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X22 @ X21 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('87',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('88',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('89',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_wellord1 @ X24 @ X23 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X23 @ X24 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X2 @ ( k2_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( m1_subset_1 @ X2 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( m1_subset_1 @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['87','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( m1_subset_1 @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( m1_subset_1 @ sk_A @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['86','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( m1_subset_1 @ sk_A @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('102',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ( v1_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('104',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['102','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('107',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( v1_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B ) )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( v1_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X22 @ X21 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('114',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('115',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_wellord1 @ X24 @ X23 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X23 @ X24 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['113','120'])).

thf('122',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['112','123'])).

thf('125',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['85','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('129',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['83'])).

thf('134',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['83'])).

thf('136',plain,(
    ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['84','136'])).

thf('138',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['82','137'])).

thf('139',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('140',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X12: $i] :
      ( ( ( k3_relat_1 @ X12 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['64'])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['142','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      | ( X1
        = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k3_xboole_0 @ ( k3_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['141','148'])).

thf('150',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['140','151'])).

thf('153',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['84','136'])).

thf('156',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('158',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('160',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('164',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('168',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('171',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['84','136'])).

thf('175',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['173','174'])).

thf('176',plain,(
    m1_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','175'])).

thf('177',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('178',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('180',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['84','136'])).

thf('184',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['182','183'])).

thf('185',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k2_wellord1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','184'])).

thf('186',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('187',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('191',plain,
    ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['173','174'])).

thf('193',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    $false ),
    inference(demod,[status(thm)],['191','192','193'])).


%------------------------------------------------------------------------------

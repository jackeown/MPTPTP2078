%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DWOZAhzrdY

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:30 EST 2020

% Result     : Theorem 3.51s
% Output     : Refutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 245 expanded)
%              Number of leaves         :   23 (  80 expanded)
%              Depth                    :   28
%              Number of atoms          :  886 (2394 expanded)
%              Number of equality atoms :   62 ( 162 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k10_relat_1 @ X17 @ ( k6_subset_1 @ X18 @ X19 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X17 @ X18 ) @ ( k10_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k10_relat_1 @ X17 @ ( k6_subset_1 @ X18 @ X19 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X17 @ X18 ) @ ( k10_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

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

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( r1_tarski @ X22 @ ( k10_relat_1 @ X23 @ ( k9_relat_1 @ X23 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X13 @ X14 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('13',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k6_subset_1 @ X1 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k6_subset_1 @ X1 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t147_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
         => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t147_funct_1])).

thf('17',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X9 @ X10 ) @ X9 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf(t174_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
          & ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( r1_tarski @ X15 @ ( k2_relat_1 @ X16 ) )
      | ( ( k10_relat_1 @ X16 @ X15 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t174_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k6_subset_1 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
       != k1_xboole_0 )
      | ( ( k6_subset_1 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X13 @ X14 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('35',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k10_relat_1 @ X17 @ ( k6_subset_1 @ X18 @ X19 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X17 @ X18 ) @ ( k10_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k6_subset_1 @ X1 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k6_subset_1 @ X1 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
      = ( k6_subset_1 @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['32','41'])).

thf('43',plain,
    ( ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k6_subset_1 @ X1 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('45',plain,
    ( ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( k1_xboole_0
    = ( k6_subset_1 @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','48','49','50'])).

thf('52',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('53',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('54',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k6_subset_1 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( r1_tarski @ X22 @ ( k10_relat_1 @ X23 @ ( k9_relat_1 @ X23 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('62',plain,
    ( ( k6_subset_1 @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
       != k1_xboole_0 )
      | ( ( k6_subset_1 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('68',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k6_subset_1 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('71',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    r1_tarski @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('73',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X20 @ ( k10_relat_1 @ X20 @ X21 ) ) @ X21 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('74',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_A
      = ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( sk_A
    = ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['79','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DWOZAhzrdY
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.51/3.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.51/3.69  % Solved by: fo/fo7.sh
% 3.51/3.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.51/3.69  % done 5615 iterations in 3.233s
% 3.51/3.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.51/3.69  % SZS output start Refutation
% 3.51/3.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.51/3.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.51/3.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.51/3.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.51/3.69  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 3.51/3.69  thf(sk_B_type, type, sk_B: $i).
% 3.51/3.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.51/3.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.51/3.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.51/3.69  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 3.51/3.69  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.51/3.69  thf(sk_A_type, type, sk_A: $i).
% 3.51/3.69  thf(t138_funct_1, axiom,
% 3.51/3.69    (![A:$i,B:$i,C:$i]:
% 3.51/3.69     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 3.51/3.69       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 3.51/3.69         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 3.51/3.69  thf('0', plain,
% 3.51/3.69      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.51/3.69         (((k10_relat_1 @ X17 @ (k6_subset_1 @ X18 @ X19))
% 3.51/3.69            = (k6_subset_1 @ (k10_relat_1 @ X17 @ X18) @ 
% 3.51/3.69               (k10_relat_1 @ X17 @ X19)))
% 3.51/3.69          | ~ (v1_funct_1 @ X17)
% 3.51/3.69          | ~ (v1_relat_1 @ X17))),
% 3.51/3.69      inference('cnf', [status(esa)], [t138_funct_1])).
% 3.51/3.69  thf('1', plain,
% 3.51/3.69      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.51/3.69         (((k10_relat_1 @ X17 @ (k6_subset_1 @ X18 @ X19))
% 3.51/3.69            = (k6_subset_1 @ (k10_relat_1 @ X17 @ X18) @ 
% 3.51/3.69               (k10_relat_1 @ X17 @ X19)))
% 3.51/3.69          | ~ (v1_funct_1 @ X17)
% 3.51/3.69          | ~ (v1_relat_1 @ X17))),
% 3.51/3.69      inference('cnf', [status(esa)], [t138_funct_1])).
% 3.51/3.69  thf(d10_xboole_0, axiom,
% 3.51/3.69    (![A:$i,B:$i]:
% 3.51/3.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.51/3.69  thf('2', plain,
% 3.51/3.69      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.51/3.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.51/3.69  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.51/3.69      inference('simplify', [status(thm)], ['2'])).
% 3.51/3.69  thf(t146_funct_1, axiom,
% 3.51/3.69    (![A:$i,B:$i]:
% 3.51/3.69     ( ( v1_relat_1 @ B ) =>
% 3.51/3.69       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 3.51/3.69         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 3.51/3.69  thf('4', plain,
% 3.51/3.69      (![X22 : $i, X23 : $i]:
% 3.51/3.69         (~ (r1_tarski @ X22 @ (k1_relat_1 @ X23))
% 3.51/3.69          | (r1_tarski @ X22 @ (k10_relat_1 @ X23 @ (k9_relat_1 @ X23 @ X22)))
% 3.51/3.69          | ~ (v1_relat_1 @ X23))),
% 3.51/3.69      inference('cnf', [status(esa)], [t146_funct_1])).
% 3.51/3.69  thf('5', plain,
% 3.51/3.69      (![X0 : $i]:
% 3.51/3.69         (~ (v1_relat_1 @ X0)
% 3.51/3.69          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 3.51/3.69             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 3.51/3.69      inference('sup-', [status(thm)], ['3', '4'])).
% 3.51/3.69  thf(t167_relat_1, axiom,
% 3.51/3.69    (![A:$i,B:$i]:
% 3.51/3.69     ( ( v1_relat_1 @ B ) =>
% 3.51/3.69       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 3.51/3.69  thf('6', plain,
% 3.51/3.69      (![X13 : $i, X14 : $i]:
% 3.51/3.69         ((r1_tarski @ (k10_relat_1 @ X13 @ X14) @ (k1_relat_1 @ X13))
% 3.51/3.69          | ~ (v1_relat_1 @ X13))),
% 3.51/3.69      inference('cnf', [status(esa)], [t167_relat_1])).
% 3.51/3.69  thf(t1_xboole_1, axiom,
% 3.51/3.69    (![A:$i,B:$i,C:$i]:
% 3.51/3.69     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 3.51/3.69       ( r1_tarski @ A @ C ) ))).
% 3.51/3.69  thf('7', plain,
% 3.51/3.69      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.51/3.69         (~ (r1_tarski @ X6 @ X7)
% 3.51/3.69          | ~ (r1_tarski @ X7 @ X8)
% 3.51/3.69          | (r1_tarski @ X6 @ X8))),
% 3.51/3.69      inference('cnf', [status(esa)], [t1_xboole_1])).
% 3.51/3.69  thf('8', plain,
% 3.51/3.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.51/3.69         (~ (v1_relat_1 @ X0)
% 3.51/3.69          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ X2)
% 3.51/3.69          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ X2))),
% 3.51/3.69      inference('sup-', [status(thm)], ['6', '7'])).
% 3.51/3.69  thf('9', plain,
% 3.51/3.69      (![X0 : $i, X1 : $i]:
% 3.51/3.69         (~ (v1_relat_1 @ X0)
% 3.51/3.69          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ 
% 3.51/3.69             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 3.51/3.69          | ~ (v1_relat_1 @ X0))),
% 3.51/3.69      inference('sup-', [status(thm)], ['5', '8'])).
% 3.51/3.69  thf('10', plain,
% 3.51/3.69      (![X0 : $i, X1 : $i]:
% 3.51/3.69         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ 
% 3.51/3.69           (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 3.51/3.69          | ~ (v1_relat_1 @ X0))),
% 3.51/3.69      inference('simplify', [status(thm)], ['9'])).
% 3.51/3.69  thf(l32_xboole_1, axiom,
% 3.51/3.69    (![A:$i,B:$i]:
% 3.51/3.69     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.51/3.69  thf('11', plain,
% 3.51/3.69      (![X3 : $i, X5 : $i]:
% 3.51/3.69         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 3.51/3.69      inference('cnf', [status(esa)], [l32_xboole_1])).
% 3.51/3.69  thf(redefinition_k6_subset_1, axiom,
% 3.51/3.69    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 3.51/3.69  thf('12', plain,
% 3.51/3.69      (![X11 : $i, X12 : $i]:
% 3.51/3.69         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 3.51/3.69      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.51/3.69  thf('13', plain,
% 3.51/3.69      (![X3 : $i, X5 : $i]:
% 3.51/3.69         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 3.51/3.69      inference('demod', [status(thm)], ['11', '12'])).
% 3.51/3.69  thf('14', plain,
% 3.51/3.69      (![X0 : $i, X1 : $i]:
% 3.51/3.69         (~ (v1_relat_1 @ X0)
% 3.51/3.69          | ((k6_subset_1 @ (k10_relat_1 @ X0 @ X1) @ 
% 3.51/3.69              (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 3.51/3.69              = (k1_xboole_0)))),
% 3.51/3.69      inference('sup-', [status(thm)], ['10', '13'])).
% 3.51/3.69  thf('15', plain,
% 3.51/3.69      (![X0 : $i, X1 : $i]:
% 3.51/3.69         (((k10_relat_1 @ X0 @ 
% 3.51/3.69            (k6_subset_1 @ X1 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 3.51/3.69            = (k1_xboole_0))
% 3.51/3.69          | ~ (v1_relat_1 @ X0)
% 3.51/3.69          | ~ (v1_funct_1 @ X0)
% 3.51/3.69          | ~ (v1_relat_1 @ X0))),
% 3.51/3.69      inference('sup+', [status(thm)], ['1', '14'])).
% 3.51/3.69  thf('16', plain,
% 3.51/3.69      (![X0 : $i, X1 : $i]:
% 3.51/3.69         (~ (v1_funct_1 @ X0)
% 3.51/3.69          | ~ (v1_relat_1 @ X0)
% 3.51/3.69          | ((k10_relat_1 @ X0 @ 
% 3.51/3.69              (k6_subset_1 @ X1 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 3.51/3.69              = (k1_xboole_0)))),
% 3.51/3.69      inference('simplify', [status(thm)], ['15'])).
% 3.51/3.69  thf(t147_funct_1, conjecture,
% 3.51/3.69    (![A:$i,B:$i]:
% 3.51/3.69     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.51/3.69       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 3.51/3.69         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 3.51/3.69  thf(zf_stmt_0, negated_conjecture,
% 3.51/3.69    (~( ![A:$i,B:$i]:
% 3.51/3.69        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.51/3.69          ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 3.51/3.69            ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 3.51/3.69    inference('cnf.neg', [status(esa)], [t147_funct_1])).
% 3.51/3.69  thf('17', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 3.51/3.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.69  thf(t36_xboole_1, axiom,
% 3.51/3.69    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 3.51/3.69  thf('18', plain,
% 3.51/3.69      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 3.51/3.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.51/3.69  thf('19', plain,
% 3.51/3.69      (![X11 : $i, X12 : $i]:
% 3.51/3.69         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 3.51/3.69      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.51/3.69  thf('20', plain,
% 3.51/3.69      (![X9 : $i, X10 : $i]: (r1_tarski @ (k6_subset_1 @ X9 @ X10) @ X9)),
% 3.51/3.69      inference('demod', [status(thm)], ['18', '19'])).
% 3.51/3.69  thf('21', plain,
% 3.51/3.69      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.51/3.69         (~ (r1_tarski @ X6 @ X7)
% 3.51/3.69          | ~ (r1_tarski @ X7 @ X8)
% 3.51/3.69          | (r1_tarski @ X6 @ X8))),
% 3.51/3.69      inference('cnf', [status(esa)], [t1_xboole_1])).
% 3.51/3.69  thf('22', plain,
% 3.51/3.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.51/3.69         ((r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 3.51/3.69      inference('sup-', [status(thm)], ['20', '21'])).
% 3.51/3.69  thf('23', plain,
% 3.51/3.69      (![X0 : $i]:
% 3.51/3.69         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_B))),
% 3.51/3.69      inference('sup-', [status(thm)], ['17', '22'])).
% 3.51/3.69  thf(t174_relat_1, axiom,
% 3.51/3.69    (![A:$i,B:$i]:
% 3.51/3.69     ( ( v1_relat_1 @ B ) =>
% 3.51/3.69       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 3.51/3.69            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 3.51/3.69            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 3.51/3.69  thf('24', plain,
% 3.51/3.69      (![X15 : $i, X16 : $i]:
% 3.51/3.69         (((X15) = (k1_xboole_0))
% 3.51/3.69          | ~ (v1_relat_1 @ X16)
% 3.51/3.69          | ~ (r1_tarski @ X15 @ (k2_relat_1 @ X16))
% 3.51/3.69          | ((k10_relat_1 @ X16 @ X15) != (k1_xboole_0)))),
% 3.51/3.69      inference('cnf', [status(esa)], [t174_relat_1])).
% 3.51/3.69  thf('25', plain,
% 3.51/3.69      (![X0 : $i]:
% 3.51/3.69         (((k10_relat_1 @ sk_B @ (k6_subset_1 @ sk_A @ X0)) != (k1_xboole_0))
% 3.51/3.69          | ~ (v1_relat_1 @ sk_B)
% 3.51/3.69          | ((k6_subset_1 @ sk_A @ X0) = (k1_xboole_0)))),
% 3.51/3.69      inference('sup-', [status(thm)], ['23', '24'])).
% 3.51/3.69  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 3.51/3.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.69  thf('27', plain,
% 3.51/3.69      (![X0 : $i]:
% 3.51/3.69         (((k10_relat_1 @ sk_B @ (k6_subset_1 @ sk_A @ X0)) != (k1_xboole_0))
% 3.51/3.69          | ((k6_subset_1 @ sk_A @ X0) = (k1_xboole_0)))),
% 3.51/3.69      inference('demod', [status(thm)], ['25', '26'])).
% 3.51/3.69  thf('28', plain,
% 3.51/3.69      ((((k1_xboole_0) != (k1_xboole_0))
% 3.51/3.69        | ~ (v1_relat_1 @ sk_B)
% 3.51/3.69        | ~ (v1_funct_1 @ sk_B)
% 3.51/3.69        | ((k6_subset_1 @ sk_A @ (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 3.51/3.69            = (k1_xboole_0)))),
% 3.51/3.69      inference('sup-', [status(thm)], ['16', '27'])).
% 3.51/3.69  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 3.51/3.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.69  thf('30', plain, ((v1_funct_1 @ sk_B)),
% 3.51/3.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.69  thf('31', plain,
% 3.51/3.69      ((((k1_xboole_0) != (k1_xboole_0))
% 3.51/3.69        | ((k6_subset_1 @ sk_A @ (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 3.51/3.69            = (k1_xboole_0)))),
% 3.51/3.69      inference('demod', [status(thm)], ['28', '29', '30'])).
% 3.51/3.69  thf('32', plain,
% 3.51/3.69      (((k6_subset_1 @ sk_A @ (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 3.51/3.69         = (k1_xboole_0))),
% 3.51/3.69      inference('simplify', [status(thm)], ['31'])).
% 3.51/3.69  thf('33', plain,
% 3.51/3.69      (![X0 : $i]:
% 3.51/3.69         (~ (v1_relat_1 @ X0)
% 3.51/3.69          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 3.51/3.69             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 3.51/3.69      inference('sup-', [status(thm)], ['3', '4'])).
% 3.51/3.69  thf('34', plain,
% 3.51/3.69      (![X13 : $i, X14 : $i]:
% 3.51/3.69         ((r1_tarski @ (k10_relat_1 @ X13 @ X14) @ (k1_relat_1 @ X13))
% 3.51/3.69          | ~ (v1_relat_1 @ X13))),
% 3.51/3.69      inference('cnf', [status(esa)], [t167_relat_1])).
% 3.51/3.69  thf('35', plain,
% 3.51/3.69      (![X0 : $i, X2 : $i]:
% 3.51/3.69         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.51/3.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.51/3.69  thf('36', plain,
% 3.51/3.69      (![X0 : $i, X1 : $i]:
% 3.51/3.69         (~ (v1_relat_1 @ X0)
% 3.51/3.69          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 3.51/3.69          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 3.51/3.69      inference('sup-', [status(thm)], ['34', '35'])).
% 3.51/3.69  thf('37', plain,
% 3.51/3.69      (![X0 : $i]:
% 3.51/3.69         (~ (v1_relat_1 @ X0)
% 3.51/3.69          | ((k1_relat_1 @ X0)
% 3.51/3.69              = (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 3.51/3.69          | ~ (v1_relat_1 @ X0))),
% 3.51/3.69      inference('sup-', [status(thm)], ['33', '36'])).
% 3.51/3.69  thf('38', plain,
% 3.51/3.69      (![X0 : $i]:
% 3.51/3.69         (((k1_relat_1 @ X0)
% 3.51/3.69            = (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 3.51/3.69          | ~ (v1_relat_1 @ X0))),
% 3.51/3.69      inference('simplify', [status(thm)], ['37'])).
% 3.51/3.69  thf('39', plain,
% 3.51/3.69      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.51/3.69         (((k10_relat_1 @ X17 @ (k6_subset_1 @ X18 @ X19))
% 3.51/3.69            = (k6_subset_1 @ (k10_relat_1 @ X17 @ X18) @ 
% 3.51/3.69               (k10_relat_1 @ X17 @ X19)))
% 3.51/3.69          | ~ (v1_funct_1 @ X17)
% 3.51/3.69          | ~ (v1_relat_1 @ X17))),
% 3.51/3.69      inference('cnf', [status(esa)], [t138_funct_1])).
% 3.51/3.69  thf('40', plain,
% 3.51/3.69      (![X0 : $i, X1 : $i]:
% 3.51/3.69         (((k10_relat_1 @ X0 @ 
% 3.51/3.69            (k6_subset_1 @ X1 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 3.51/3.69            = (k6_subset_1 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))
% 3.51/3.69          | ~ (v1_relat_1 @ X0)
% 3.51/3.69          | ~ (v1_relat_1 @ X0)
% 3.51/3.69          | ~ (v1_funct_1 @ X0))),
% 3.51/3.69      inference('sup+', [status(thm)], ['38', '39'])).
% 3.51/3.69  thf('41', plain,
% 3.51/3.69      (![X0 : $i, X1 : $i]:
% 3.51/3.69         (~ (v1_funct_1 @ X0)
% 3.51/3.69          | ~ (v1_relat_1 @ X0)
% 3.51/3.69          | ((k10_relat_1 @ X0 @ 
% 3.51/3.69              (k6_subset_1 @ X1 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 3.51/3.69              = (k6_subset_1 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))))),
% 3.51/3.69      inference('simplify', [status(thm)], ['40'])).
% 3.51/3.69  thf('42', plain,
% 3.51/3.69      ((((k10_relat_1 @ sk_B @ k1_xboole_0)
% 3.51/3.69          = (k6_subset_1 @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B)))
% 3.51/3.69        | ~ (v1_relat_1 @ sk_B)
% 3.51/3.69        | ~ (v1_funct_1 @ sk_B))),
% 3.51/3.69      inference('sup+', [status(thm)], ['32', '41'])).
% 3.51/3.69  thf('43', plain,
% 3.51/3.69      (((k6_subset_1 @ sk_A @ (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 3.51/3.69         = (k1_xboole_0))),
% 3.51/3.69      inference('simplify', [status(thm)], ['31'])).
% 3.51/3.69  thf('44', plain,
% 3.51/3.69      (![X0 : $i, X1 : $i]:
% 3.51/3.69         (~ (v1_funct_1 @ X0)
% 3.51/3.69          | ~ (v1_relat_1 @ X0)
% 3.51/3.69          | ((k10_relat_1 @ X0 @ 
% 3.51/3.69              (k6_subset_1 @ X1 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 3.51/3.69              = (k1_xboole_0)))),
% 3.51/3.69      inference('simplify', [status(thm)], ['15'])).
% 3.51/3.69  thf('45', plain,
% 3.51/3.69      ((((k10_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))
% 3.51/3.69        | ~ (v1_relat_1 @ sk_B)
% 3.51/3.69        | ~ (v1_funct_1 @ sk_B))),
% 3.51/3.69      inference('sup+', [status(thm)], ['43', '44'])).
% 3.51/3.69  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 3.51/3.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.69  thf('47', plain, ((v1_funct_1 @ sk_B)),
% 3.51/3.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.69  thf('48', plain, (((k10_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 3.51/3.69      inference('demod', [status(thm)], ['45', '46', '47'])).
% 3.51/3.69  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 3.51/3.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.69  thf('50', plain, ((v1_funct_1 @ sk_B)),
% 3.51/3.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.69  thf('51', plain,
% 3.51/3.69      (((k1_xboole_0)
% 3.51/3.69         = (k6_subset_1 @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 3.51/3.69      inference('demod', [status(thm)], ['42', '48', '49', '50'])).
% 3.51/3.69  thf('52', plain,
% 3.51/3.69      (![X3 : $i, X4 : $i]:
% 3.51/3.69         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 3.51/3.69      inference('cnf', [status(esa)], [l32_xboole_1])).
% 3.51/3.69  thf('53', plain,
% 3.51/3.69      (![X11 : $i, X12 : $i]:
% 3.51/3.69         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 3.51/3.69      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.51/3.69  thf('54', plain,
% 3.51/3.69      (![X3 : $i, X4 : $i]:
% 3.51/3.69         ((r1_tarski @ X3 @ X4) | ((k6_subset_1 @ X3 @ X4) != (k1_xboole_0)))),
% 3.51/3.69      inference('demod', [status(thm)], ['52', '53'])).
% 3.51/3.69  thf('55', plain,
% 3.51/3.69      ((((k1_xboole_0) != (k1_xboole_0))
% 3.51/3.69        | (r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 3.51/3.69      inference('sup-', [status(thm)], ['51', '54'])).
% 3.51/3.69  thf('56', plain,
% 3.51/3.69      ((r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B))),
% 3.51/3.69      inference('simplify', [status(thm)], ['55'])).
% 3.51/3.69  thf('57', plain,
% 3.51/3.69      (![X22 : $i, X23 : $i]:
% 3.51/3.69         (~ (r1_tarski @ X22 @ (k1_relat_1 @ X23))
% 3.51/3.69          | (r1_tarski @ X22 @ (k10_relat_1 @ X23 @ (k9_relat_1 @ X23 @ X22)))
% 3.51/3.69          | ~ (v1_relat_1 @ X23))),
% 3.51/3.69      inference('cnf', [status(esa)], [t146_funct_1])).
% 3.51/3.69  thf('58', plain,
% 3.51/3.69      ((~ (v1_relat_1 @ sk_B)
% 3.51/3.69        | (r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ 
% 3.51/3.69           (k10_relat_1 @ sk_B @ 
% 3.51/3.69            (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))))),
% 3.51/3.69      inference('sup-', [status(thm)], ['56', '57'])).
% 3.51/3.69  thf('59', plain, ((v1_relat_1 @ sk_B)),
% 3.51/3.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.69  thf('60', plain,
% 3.51/3.69      ((r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ 
% 3.51/3.69        (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))),
% 3.51/3.69      inference('demod', [status(thm)], ['58', '59'])).
% 3.51/3.69  thf('61', plain,
% 3.51/3.69      (![X3 : $i, X5 : $i]:
% 3.51/3.69         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 3.51/3.69      inference('demod', [status(thm)], ['11', '12'])).
% 3.51/3.69  thf('62', plain,
% 3.51/3.69      (((k6_subset_1 @ (k10_relat_1 @ sk_B @ sk_A) @ 
% 3.51/3.69         (k10_relat_1 @ sk_B @ 
% 3.51/3.69          (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))
% 3.51/3.69         = (k1_xboole_0))),
% 3.51/3.69      inference('sup-', [status(thm)], ['60', '61'])).
% 3.51/3.69  thf('63', plain,
% 3.51/3.69      ((((k10_relat_1 @ sk_B @ 
% 3.51/3.69          (k6_subset_1 @ sk_A @ 
% 3.51/3.69           (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))
% 3.51/3.69          = (k1_xboole_0))
% 3.51/3.69        | ~ (v1_relat_1 @ sk_B)
% 3.51/3.69        | ~ (v1_funct_1 @ sk_B))),
% 3.51/3.69      inference('sup+', [status(thm)], ['0', '62'])).
% 3.51/3.69  thf('64', plain, ((v1_relat_1 @ sk_B)),
% 3.51/3.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.69  thf('65', plain, ((v1_funct_1 @ sk_B)),
% 3.51/3.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.69  thf('66', plain,
% 3.51/3.69      (((k10_relat_1 @ sk_B @ 
% 3.51/3.69         (k6_subset_1 @ sk_A @ 
% 3.51/3.69          (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))
% 3.51/3.69         = (k1_xboole_0))),
% 3.51/3.69      inference('demod', [status(thm)], ['63', '64', '65'])).
% 3.51/3.69  thf('67', plain,
% 3.51/3.69      (![X0 : $i]:
% 3.51/3.69         (((k10_relat_1 @ sk_B @ (k6_subset_1 @ sk_A @ X0)) != (k1_xboole_0))
% 3.51/3.69          | ((k6_subset_1 @ sk_A @ X0) = (k1_xboole_0)))),
% 3.51/3.69      inference('demod', [status(thm)], ['25', '26'])).
% 3.51/3.69  thf('68', plain,
% 3.51/3.69      ((((k1_xboole_0) != (k1_xboole_0))
% 3.51/3.69        | ((k6_subset_1 @ sk_A @ 
% 3.51/3.69            (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))) = (k1_xboole_0)))),
% 3.51/3.69      inference('sup-', [status(thm)], ['66', '67'])).
% 3.51/3.69  thf('69', plain,
% 3.51/3.69      (((k6_subset_1 @ sk_A @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))
% 3.51/3.69         = (k1_xboole_0))),
% 3.51/3.69      inference('simplify', [status(thm)], ['68'])).
% 3.51/3.69  thf('70', plain,
% 3.51/3.69      (![X3 : $i, X4 : $i]:
% 3.51/3.69         ((r1_tarski @ X3 @ X4) | ((k6_subset_1 @ X3 @ X4) != (k1_xboole_0)))),
% 3.51/3.69      inference('demod', [status(thm)], ['52', '53'])).
% 3.51/3.69  thf('71', plain,
% 3.51/3.69      ((((k1_xboole_0) != (k1_xboole_0))
% 3.51/3.69        | (r1_tarski @ sk_A @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))),
% 3.51/3.69      inference('sup-', [status(thm)], ['69', '70'])).
% 3.51/3.69  thf('72', plain,
% 3.51/3.69      ((r1_tarski @ sk_A @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))),
% 3.51/3.69      inference('simplify', [status(thm)], ['71'])).
% 3.51/3.69  thf(t145_funct_1, axiom,
% 3.51/3.69    (![A:$i,B:$i]:
% 3.51/3.69     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.51/3.69       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 3.51/3.69  thf('73', plain,
% 3.51/3.69      (![X20 : $i, X21 : $i]:
% 3.51/3.69         ((r1_tarski @ (k9_relat_1 @ X20 @ (k10_relat_1 @ X20 @ X21)) @ X21)
% 3.51/3.69          | ~ (v1_funct_1 @ X20)
% 3.51/3.69          | ~ (v1_relat_1 @ X20))),
% 3.51/3.69      inference('cnf', [status(esa)], [t145_funct_1])).
% 3.51/3.69  thf('74', plain,
% 3.51/3.69      (![X0 : $i, X2 : $i]:
% 3.51/3.69         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.51/3.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.51/3.69  thf('75', plain,
% 3.51/3.69      (![X0 : $i, X1 : $i]:
% 3.51/3.69         (~ (v1_relat_1 @ X1)
% 3.51/3.69          | ~ (v1_funct_1 @ X1)
% 3.51/3.69          | ~ (r1_tarski @ X0 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)))
% 3.51/3.69          | ((X0) = (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))))),
% 3.51/3.69      inference('sup-', [status(thm)], ['73', '74'])).
% 3.51/3.69  thf('76', plain,
% 3.51/3.69      ((((sk_A) = (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))
% 3.51/3.69        | ~ (v1_funct_1 @ sk_B)
% 3.51/3.69        | ~ (v1_relat_1 @ sk_B))),
% 3.51/3.69      inference('sup-', [status(thm)], ['72', '75'])).
% 3.51/3.69  thf('77', plain, ((v1_funct_1 @ sk_B)),
% 3.51/3.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.69  thf('78', plain, ((v1_relat_1 @ sk_B)),
% 3.51/3.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.69  thf('79', plain,
% 3.51/3.69      (((sk_A) = (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))),
% 3.51/3.69      inference('demod', [status(thm)], ['76', '77', '78'])).
% 3.51/3.69  thf('80', plain,
% 3.51/3.69      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 3.51/3.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.69  thf('81', plain, ($false),
% 3.51/3.69      inference('simplify_reflect-', [status(thm)], ['79', '80'])).
% 3.51/3.69  
% 3.51/3.69  % SZS output end Refutation
% 3.51/3.69  
% 3.51/3.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

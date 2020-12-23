%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vy1jwY8Ax0

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:53 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 184 expanded)
%              Number of leaves         :   23 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  668 (1637 expanded)
%              Number of equality atoms :   33 (  58 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t158_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t158_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ X1 @ X1 ) )
      | ( X0
        = ( k6_subset_1 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) )
      = ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('16',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ X25 @ ( k6_subset_1 @ X26 @ X27 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X25 @ X26 ) @ ( k10_relat_1 @ X25 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k6_subset_1 @ X0 @ X0 ) )
        = ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('20',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X8 @ X9 ) @ X8 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('25',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X28 @ ( k2_relat_1 @ X29 ) )
      | ( ( k9_relat_1 @ X29 @ ( k10_relat_1 @ X29 @ X28 ) )
        = X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
        = ( k6_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
      = ( k6_subset_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) )
      = ( k6_subset_1 @ sk_A @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['17','29'])).

thf('31',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ X25 @ ( k6_subset_1 @ X26 @ X27 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X25 @ X26 ) @ ( k10_relat_1 @ X25 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('32',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('33',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k2_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['31','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) ) @ X0 ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('44',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) )
      | ( X0
        = ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
      = ( k6_subset_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('48',plain,
    ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['30','48','49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ X1 @ X1 ) )
      | ( X0
        = ( k6_subset_1 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ X1 )
      = ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['55'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('57',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17
        = ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('58',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('59',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17
        = ( k2_xboole_0 @ X16 @ ( k6_subset_1 @ X17 @ X16 ) ) )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k6_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['51','61'])).

thf('63',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['55'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('64',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('65',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('66',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['62','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['0','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vy1jwY8Ax0
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.52/1.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.52/1.74  % Solved by: fo/fo7.sh
% 1.52/1.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.52/1.74  % done 2803 iterations in 1.283s
% 1.52/1.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.52/1.74  % SZS output start Refutation
% 1.52/1.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.52/1.74  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.52/1.74  thf(sk_B_type, type, sk_B: $i).
% 1.52/1.74  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.52/1.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.52/1.74  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.52/1.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.52/1.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.52/1.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.52/1.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.52/1.74  thf(sk_A_type, type, sk_A: $i).
% 1.52/1.74  thf(sk_C_type, type, sk_C: $i).
% 1.52/1.74  thf(t158_funct_1, conjecture,
% 1.52/1.74    (![A:$i,B:$i,C:$i]:
% 1.52/1.74     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.52/1.74       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 1.52/1.74           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 1.52/1.74         ( r1_tarski @ A @ B ) ) ))).
% 1.52/1.74  thf(zf_stmt_0, negated_conjecture,
% 1.52/1.74    (~( ![A:$i,B:$i,C:$i]:
% 1.52/1.74        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.52/1.74          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 1.52/1.74              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 1.52/1.74            ( r1_tarski @ A @ B ) ) ) )),
% 1.52/1.74    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 1.52/1.74  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf(t7_xboole_1, axiom,
% 1.52/1.74    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.52/1.74  thf('1', plain,
% 1.52/1.74      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 1.52/1.74      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.52/1.74  thf('2', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf(t1_xboole_1, axiom,
% 1.52/1.74    (![A:$i,B:$i,C:$i]:
% 1.52/1.74     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.52/1.74       ( r1_tarski @ A @ C ) ))).
% 1.52/1.74  thf('3', plain,
% 1.52/1.74      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.52/1.74         (~ (r1_tarski @ X5 @ X6)
% 1.52/1.74          | ~ (r1_tarski @ X6 @ X7)
% 1.52/1.74          | (r1_tarski @ X5 @ X7))),
% 1.52/1.74      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.52/1.74  thf('4', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0))),
% 1.52/1.74      inference('sup-', [status(thm)], ['2', '3'])).
% 1.52/1.74  thf('5', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (r1_tarski @ sk_A @ (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ X0))),
% 1.52/1.74      inference('sup-', [status(thm)], ['1', '4'])).
% 1.52/1.74  thf(t43_xboole_1, axiom,
% 1.52/1.74    (![A:$i,B:$i,C:$i]:
% 1.52/1.74     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.52/1.74       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.52/1.74  thf('6', plain,
% 1.52/1.74      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.52/1.74         ((r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 1.52/1.74          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 1.52/1.74      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.52/1.74  thf(redefinition_k6_subset_1, axiom,
% 1.52/1.74    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.52/1.74  thf('7', plain,
% 1.52/1.74      (![X23 : $i, X24 : $i]:
% 1.52/1.74         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 1.52/1.74      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.52/1.74  thf('8', plain,
% 1.52/1.74      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.52/1.74         ((r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X12)
% 1.52/1.74          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 1.52/1.74      inference('demod', [status(thm)], ['6', '7'])).
% 1.52/1.74  thf('9', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (r1_tarski @ (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)) @ X0)),
% 1.52/1.74      inference('sup-', [status(thm)], ['5', '8'])).
% 1.52/1.74  thf('10', plain,
% 1.52/1.74      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 1.52/1.74      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.52/1.74  thf('11', plain,
% 1.52/1.74      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.52/1.74         ((r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X12)
% 1.52/1.74          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 1.52/1.74      inference('demod', [status(thm)], ['6', '7'])).
% 1.52/1.74  thf('12', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X1 @ X1) @ X0)),
% 1.52/1.74      inference('sup-', [status(thm)], ['10', '11'])).
% 1.52/1.74  thf(d10_xboole_0, axiom,
% 1.52/1.74    (![A:$i,B:$i]:
% 1.52/1.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.52/1.74  thf('13', plain,
% 1.52/1.74      (![X0 : $i, X2 : $i]:
% 1.52/1.74         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.52/1.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.52/1.74  thf('14', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X1 @ X1))
% 1.52/1.74          | ((X0) = (k6_subset_1 @ X1 @ X1)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['12', '13'])).
% 1.52/1.74  thf('15', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)) = (k6_subset_1 @ X0 @ X0))),
% 1.52/1.74      inference('sup-', [status(thm)], ['9', '14'])).
% 1.52/1.74  thf(t138_funct_1, axiom,
% 1.52/1.74    (![A:$i,B:$i,C:$i]:
% 1.52/1.74     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.52/1.74       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 1.52/1.74         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.52/1.74  thf('16', plain,
% 1.52/1.74      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.52/1.74         (((k10_relat_1 @ X25 @ (k6_subset_1 @ X26 @ X27))
% 1.52/1.74            = (k6_subset_1 @ (k10_relat_1 @ X25 @ X26) @ 
% 1.52/1.74               (k10_relat_1 @ X25 @ X27)))
% 1.52/1.74          | ~ (v1_funct_1 @ X25)
% 1.52/1.74          | ~ (v1_relat_1 @ X25))),
% 1.52/1.74      inference('cnf', [status(esa)], [t138_funct_1])).
% 1.52/1.74  thf('17', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         (((k10_relat_1 @ X1 @ (k6_subset_1 @ X0 @ X0))
% 1.52/1.74            = (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)))
% 1.52/1.74          | ~ (v1_relat_1 @ X1)
% 1.52/1.74          | ~ (v1_funct_1 @ X1))),
% 1.52/1.74      inference('sup+', [status(thm)], ['15', '16'])).
% 1.52/1.74  thf('18', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf(t36_xboole_1, axiom,
% 1.52/1.74    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.52/1.74  thf('19', plain,
% 1.52/1.74      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 1.52/1.74      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.52/1.74  thf('20', plain,
% 1.52/1.74      (![X23 : $i, X24 : $i]:
% 1.52/1.74         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 1.52/1.74      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.52/1.74  thf('21', plain,
% 1.52/1.74      (![X8 : $i, X9 : $i]: (r1_tarski @ (k6_subset_1 @ X8 @ X9) @ X8)),
% 1.52/1.74      inference('demod', [status(thm)], ['19', '20'])).
% 1.52/1.74  thf('22', plain,
% 1.52/1.74      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.52/1.74         (~ (r1_tarski @ X5 @ X6)
% 1.52/1.74          | ~ (r1_tarski @ X6 @ X7)
% 1.52/1.74          | (r1_tarski @ X5 @ X7))),
% 1.52/1.74      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.52/1.74  thf('23', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.52/1.74         ((r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 1.52/1.74      inference('sup-', [status(thm)], ['21', '22'])).
% 1.52/1.74  thf('24', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_C))),
% 1.52/1.74      inference('sup-', [status(thm)], ['18', '23'])).
% 1.52/1.74  thf(t147_funct_1, axiom,
% 1.52/1.74    (![A:$i,B:$i]:
% 1.52/1.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.52/1.74       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.52/1.74         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.52/1.74  thf('25', plain,
% 1.52/1.74      (![X28 : $i, X29 : $i]:
% 1.52/1.74         (~ (r1_tarski @ X28 @ (k2_relat_1 @ X29))
% 1.52/1.74          | ((k9_relat_1 @ X29 @ (k10_relat_1 @ X29 @ X28)) = (X28))
% 1.52/1.74          | ~ (v1_funct_1 @ X29)
% 1.52/1.74          | ~ (v1_relat_1 @ X29))),
% 1.52/1.74      inference('cnf', [status(esa)], [t147_funct_1])).
% 1.52/1.74  thf('26', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (v1_relat_1 @ sk_C)
% 1.52/1.74          | ~ (v1_funct_1 @ sk_C)
% 1.52/1.74          | ((k9_relat_1 @ sk_C @ 
% 1.52/1.74              (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 1.52/1.74              = (k6_subset_1 @ sk_A @ X0)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['24', '25'])).
% 1.52/1.74  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('29', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 1.52/1.74           = (k6_subset_1 @ sk_A @ X0))),
% 1.52/1.74      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.52/1.74  thf('30', plain,
% 1.52/1.74      ((((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)))
% 1.52/1.74          = (k6_subset_1 @ sk_A @ sk_A))
% 1.52/1.74        | ~ (v1_funct_1 @ sk_C)
% 1.52/1.74        | ~ (v1_relat_1 @ sk_C))),
% 1.52/1.74      inference('sup+', [status(thm)], ['17', '29'])).
% 1.52/1.74  thf('31', plain,
% 1.52/1.74      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.52/1.74         (((k10_relat_1 @ X25 @ (k6_subset_1 @ X26 @ X27))
% 1.52/1.74            = (k6_subset_1 @ (k10_relat_1 @ X25 @ X26) @ 
% 1.52/1.74               (k10_relat_1 @ X25 @ X27)))
% 1.52/1.74          | ~ (v1_funct_1 @ X25)
% 1.52/1.74          | ~ (v1_relat_1 @ X25))),
% 1.52/1.74      inference('cnf', [status(esa)], [t138_funct_1])).
% 1.52/1.74  thf('32', plain,
% 1.52/1.74      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 1.52/1.74      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.52/1.74  thf('33', plain,
% 1.52/1.74      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('34', plain,
% 1.52/1.74      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.52/1.74         (~ (r1_tarski @ X5 @ X6)
% 1.52/1.74          | ~ (r1_tarski @ X6 @ X7)
% 1.52/1.74          | (r1_tarski @ X5 @ X7))),
% 1.52/1.74      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.52/1.74  thf('35', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ X0)
% 1.52/1.74          | ~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_B) @ X0))),
% 1.52/1.74      inference('sup-', [status(thm)], ['33', '34'])).
% 1.52/1.74  thf('36', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 1.52/1.74          (k2_xboole_0 @ (k10_relat_1 @ sk_C @ sk_B) @ X0))),
% 1.52/1.74      inference('sup-', [status(thm)], ['32', '35'])).
% 1.52/1.74  thf('37', plain,
% 1.52/1.74      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.52/1.74         ((r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X12)
% 1.52/1.74          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 1.52/1.74      inference('demod', [status(thm)], ['6', '7'])).
% 1.52/1.74  thf('38', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (r1_tarski @ 
% 1.52/1.74          (k6_subset_1 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 1.52/1.74           (k10_relat_1 @ sk_C @ sk_B)) @ 
% 1.52/1.74          X0)),
% 1.52/1.74      inference('sup-', [status(thm)], ['36', '37'])).
% 1.52/1.74  thf('39', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((r1_tarski @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) @ X0)
% 1.52/1.74          | ~ (v1_relat_1 @ sk_C)
% 1.52/1.74          | ~ (v1_funct_1 @ sk_C))),
% 1.52/1.74      inference('sup+', [status(thm)], ['31', '38'])).
% 1.52/1.74  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('42', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (r1_tarski @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) @ X0)),
% 1.52/1.74      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.52/1.74  thf('43', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (r1_tarski @ (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)) @ X0)),
% 1.52/1.74      inference('sup-', [status(thm)], ['5', '8'])).
% 1.52/1.74  thf('44', plain,
% 1.52/1.74      (![X0 : $i, X2 : $i]:
% 1.52/1.74         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.52/1.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.52/1.74  thf('45', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (r1_tarski @ X0 @ (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)))
% 1.52/1.74          | ((X0) = (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C))))),
% 1.52/1.74      inference('sup-', [status(thm)], ['43', '44'])).
% 1.52/1.74  thf('46', plain,
% 1.52/1.74      (((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B))
% 1.52/1.74         = (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['42', '45'])).
% 1.52/1.74  thf('47', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 1.52/1.74           = (k6_subset_1 @ sk_A @ X0))),
% 1.52/1.74      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.52/1.74  thf('48', plain,
% 1.52/1.74      (((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)))
% 1.52/1.74         = (k6_subset_1 @ sk_A @ sk_B))),
% 1.52/1.74      inference('sup+', [status(thm)], ['46', '47'])).
% 1.52/1.74  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 1.52/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.74  thf('51', plain,
% 1.52/1.74      (((k6_subset_1 @ sk_A @ sk_B) = (k6_subset_1 @ sk_A @ sk_A))),
% 1.52/1.74      inference('demod', [status(thm)], ['30', '48', '49', '50'])).
% 1.52/1.74  thf('52', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X1 @ X1) @ X0)),
% 1.52/1.74      inference('sup-', [status(thm)], ['10', '11'])).
% 1.52/1.74  thf('53', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X1 @ X1))
% 1.52/1.74          | ((X0) = (k6_subset_1 @ X1 @ X1)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['12', '13'])).
% 1.52/1.74  thf('54', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]: ((k6_subset_1 @ X1 @ X1) = (k6_subset_1 @ X0 @ X0))),
% 1.52/1.74      inference('sup-', [status(thm)], ['52', '53'])).
% 1.52/1.74  thf('55', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.52/1.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.52/1.74  thf('56', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.52/1.74      inference('simplify', [status(thm)], ['55'])).
% 1.52/1.74  thf(t45_xboole_1, axiom,
% 1.52/1.74    (![A:$i,B:$i]:
% 1.52/1.74     ( ( r1_tarski @ A @ B ) =>
% 1.52/1.74       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 1.52/1.74  thf('57', plain,
% 1.52/1.74      (![X16 : $i, X17 : $i]:
% 1.52/1.74         (((X17) = (k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))
% 1.52/1.74          | ~ (r1_tarski @ X16 @ X17))),
% 1.52/1.74      inference('cnf', [status(esa)], [t45_xboole_1])).
% 1.52/1.74  thf('58', plain,
% 1.52/1.74      (![X23 : $i, X24 : $i]:
% 1.52/1.74         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 1.52/1.74      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.52/1.74  thf('59', plain,
% 1.52/1.74      (![X16 : $i, X17 : $i]:
% 1.52/1.74         (((X17) = (k2_xboole_0 @ X16 @ (k6_subset_1 @ X17 @ X16)))
% 1.52/1.74          | ~ (r1_tarski @ X16 @ X17))),
% 1.52/1.74      inference('demod', [status(thm)], ['57', '58'])).
% 1.52/1.74  thf('60', plain,
% 1.52/1.74      (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ (k6_subset_1 @ X0 @ X0)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['56', '59'])).
% 1.52/1.74  thf('61', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         ((X1) = (k2_xboole_0 @ X1 @ (k6_subset_1 @ X0 @ X0)))),
% 1.52/1.74      inference('sup+', [status(thm)], ['54', '60'])).
% 1.52/1.74  thf('62', plain,
% 1.52/1.74      (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ (k6_subset_1 @ sk_A @ sk_B)))),
% 1.52/1.74      inference('sup+', [status(thm)], ['51', '61'])).
% 1.52/1.74  thf('63', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.52/1.74      inference('simplify', [status(thm)], ['55'])).
% 1.52/1.74  thf(t44_xboole_1, axiom,
% 1.52/1.74    (![A:$i,B:$i,C:$i]:
% 1.52/1.74     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.52/1.74       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.52/1.74  thf('64', plain,
% 1.52/1.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.52/1.74         ((r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 1.52/1.74          | ~ (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15))),
% 1.52/1.74      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.52/1.74  thf('65', plain,
% 1.52/1.74      (![X23 : $i, X24 : $i]:
% 1.52/1.74         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 1.52/1.74      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.52/1.74  thf('66', plain,
% 1.52/1.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.52/1.74         ((r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 1.52/1.74          | ~ (r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X15))),
% 1.52/1.74      inference('demod', [status(thm)], ['64', '65'])).
% 1.52/1.74  thf('67', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k6_subset_1 @ X1 @ X0)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['63', '66'])).
% 1.52/1.74  thf('68', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.52/1.74      inference('sup+', [status(thm)], ['62', '67'])).
% 1.52/1.74  thf('69', plain, ($false), inference('demod', [status(thm)], ['0', '68'])).
% 1.52/1.74  
% 1.52/1.74  % SZS output end Refutation
% 1.52/1.74  
% 1.52/1.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

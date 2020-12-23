%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SxWYLEnGGI

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:52 EST 2020

% Result     : Theorem 0.88s
% Output     : Refutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 197 expanded)
%              Number of leaves         :   23 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  656 (1713 expanded)
%              Number of equality atoms :   31 (  67 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ X1 @ X1 ) )
      | ( X0
        = ( k6_subset_1 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) )
      = ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('24',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k10_relat_1 @ X21 @ ( k6_subset_1 @ X22 @ X23 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X21 @ X22 ) @ ( k10_relat_1 @ X21 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k6_subset_1 @ X0 @ X0 ) )
        = ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X11 @ X12 ) @ X11 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k6_subset_1 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('35',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X24 @ ( k2_relat_1 @ X25 ) )
      | ( ( k9_relat_1 @ X25 @ ( k10_relat_1 @ X25 @ X24 ) )
        = X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
        = ( k6_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
      = ( k6_subset_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) )
      = ( k6_subset_1 @ sk_A @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['25','39'])).

thf('41',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k10_relat_1 @ X21 @ ( k6_subset_1 @ X22 @ X23 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X21 @ X22 ) @ ( k10_relat_1 @ X21 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('43',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('44',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k2_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['41','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) ) @ X0 ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('54',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) )
      | ( X0
        = ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
      = ( k6_subset_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('58',plain,
    ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['40','58','59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('64',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('65',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('66',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X16 @ X17 ) @ X18 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['4','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['0','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SxWYLEnGGI
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:16:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.88/1.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.88/1.06  % Solved by: fo/fo7.sh
% 0.88/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.88/1.06  % done 1524 iterations in 0.599s
% 0.88/1.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.88/1.06  % SZS output start Refutation
% 0.88/1.06  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.88/1.06  thf(sk_C_type, type, sk_C: $i).
% 0.88/1.06  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.88/1.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.88/1.06  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.88/1.06  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.88/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.88/1.06  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.88/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.88/1.06  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.88/1.06  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.88/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.88/1.06  thf(t158_funct_1, conjecture,
% 0.88/1.06    (![A:$i,B:$i,C:$i]:
% 0.88/1.06     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.88/1.06       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.88/1.06           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.88/1.06         ( r1_tarski @ A @ B ) ) ))).
% 0.88/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.88/1.06    (~( ![A:$i,B:$i,C:$i]:
% 0.88/1.06        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.88/1.06          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.88/1.06              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.88/1.06            ( r1_tarski @ A @ B ) ) ) )),
% 0.88/1.06    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 0.88/1.06  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf(d10_xboole_0, axiom,
% 0.88/1.06    (![A:$i,B:$i]:
% 0.88/1.06     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.88/1.06  thf('1', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.88/1.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.88/1.06  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.88/1.06      inference('simplify', [status(thm)], ['1'])).
% 0.88/1.06  thf(t12_xboole_1, axiom,
% 0.88/1.06    (![A:$i,B:$i]:
% 0.88/1.06     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.88/1.06  thf('3', plain,
% 0.88/1.06      (![X6 : $i, X7 : $i]:
% 0.88/1.06         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.88/1.06      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.88/1.06  thf('4', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.88/1.06      inference('sup-', [status(thm)], ['2', '3'])).
% 0.88/1.06  thf('5', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.88/1.06      inference('simplify', [status(thm)], ['1'])).
% 0.88/1.06  thf(t11_xboole_1, axiom,
% 0.88/1.06    (![A:$i,B:$i,C:$i]:
% 0.88/1.06     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.88/1.06  thf('6', plain,
% 0.88/1.06      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.88/1.06         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.88/1.06      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.88/1.06  thf('7', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.88/1.06      inference('sup-', [status(thm)], ['5', '6'])).
% 0.88/1.06  thf('8', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('9', plain,
% 0.88/1.06      (![X6 : $i, X7 : $i]:
% 0.88/1.06         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.88/1.06      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.88/1.06  thf('10', plain,
% 0.88/1.06      (((k2_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.88/1.06      inference('sup-', [status(thm)], ['8', '9'])).
% 0.88/1.06  thf('11', plain,
% 0.88/1.06      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.88/1.06         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.88/1.06      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.88/1.06  thf('12', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0) | (r1_tarski @ sk_A @ X0))),
% 0.88/1.06      inference('sup-', [status(thm)], ['10', '11'])).
% 0.88/1.06  thf('13', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (r1_tarski @ sk_A @ (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ X0))),
% 0.88/1.06      inference('sup-', [status(thm)], ['7', '12'])).
% 0.88/1.06  thf(t43_xboole_1, axiom,
% 0.88/1.06    (![A:$i,B:$i,C:$i]:
% 0.88/1.06     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.88/1.06       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.88/1.06  thf('14', plain,
% 0.88/1.06      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.88/1.06         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.88/1.06          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.88/1.06      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.88/1.06  thf(redefinition_k6_subset_1, axiom,
% 0.88/1.06    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.88/1.06  thf('15', plain,
% 0.88/1.06      (![X19 : $i, X20 : $i]:
% 0.88/1.06         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.88/1.06      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.88/1.06  thf('16', plain,
% 0.88/1.06      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.88/1.06         ((r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X15)
% 0.88/1.06          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.88/1.06      inference('demod', [status(thm)], ['14', '15'])).
% 0.88/1.06  thf('17', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (r1_tarski @ (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)) @ X0)),
% 0.88/1.06      inference('sup-', [status(thm)], ['13', '16'])).
% 0.88/1.06  thf('18', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.88/1.06      inference('sup-', [status(thm)], ['5', '6'])).
% 0.88/1.06  thf('19', plain,
% 0.88/1.06      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.88/1.06         ((r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X15)
% 0.88/1.06          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.88/1.06      inference('demod', [status(thm)], ['14', '15'])).
% 0.88/1.06  thf('20', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X1 @ X1) @ X0)),
% 0.88/1.06      inference('sup-', [status(thm)], ['18', '19'])).
% 0.88/1.06  thf('21', plain,
% 0.88/1.06      (![X0 : $i, X2 : $i]:
% 0.88/1.06         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.88/1.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.88/1.06  thf('22', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i]:
% 0.88/1.06         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X1 @ X1))
% 0.88/1.06          | ((X0) = (k6_subset_1 @ X1 @ X1)))),
% 0.88/1.06      inference('sup-', [status(thm)], ['20', '21'])).
% 0.88/1.06  thf('23', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)) = (k6_subset_1 @ X0 @ X0))),
% 0.88/1.06      inference('sup-', [status(thm)], ['17', '22'])).
% 0.88/1.06  thf(t138_funct_1, axiom,
% 0.88/1.06    (![A:$i,B:$i,C:$i]:
% 0.88/1.06     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.88/1.06       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.88/1.06         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.88/1.06  thf('24', plain,
% 0.88/1.06      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.88/1.06         (((k10_relat_1 @ X21 @ (k6_subset_1 @ X22 @ X23))
% 0.88/1.06            = (k6_subset_1 @ (k10_relat_1 @ X21 @ X22) @ 
% 0.88/1.06               (k10_relat_1 @ X21 @ X23)))
% 0.88/1.06          | ~ (v1_funct_1 @ X21)
% 0.88/1.06          | ~ (v1_relat_1 @ X21))),
% 0.88/1.06      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.88/1.06  thf('25', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i]:
% 0.88/1.06         (((k10_relat_1 @ X1 @ (k6_subset_1 @ X0 @ X0))
% 0.88/1.06            = (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)))
% 0.88/1.06          | ~ (v1_relat_1 @ X1)
% 0.88/1.06          | ~ (v1_funct_1 @ X1))),
% 0.88/1.06      inference('sup+', [status(thm)], ['23', '24'])).
% 0.88/1.06  thf('26', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf(t36_xboole_1, axiom,
% 0.88/1.06    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.88/1.06  thf('27', plain,
% 0.88/1.06      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.88/1.06      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.88/1.06  thf('28', plain,
% 0.88/1.06      (![X19 : $i, X20 : $i]:
% 0.88/1.06         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.88/1.06      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.88/1.06  thf('29', plain,
% 0.88/1.06      (![X11 : $i, X12 : $i]: (r1_tarski @ (k6_subset_1 @ X11 @ X12) @ X11)),
% 0.88/1.06      inference('demod', [status(thm)], ['27', '28'])).
% 0.88/1.06  thf('30', plain,
% 0.88/1.06      (![X6 : $i, X7 : $i]:
% 0.88/1.06         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.88/1.06      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.88/1.06  thf('31', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i]:
% 0.88/1.06         ((k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ X0) = (X0))),
% 0.88/1.06      inference('sup-', [status(thm)], ['29', '30'])).
% 0.88/1.06  thf('32', plain,
% 0.88/1.06      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.88/1.06         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.88/1.06      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.88/1.06  thf('33', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.88/1.06         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k6_subset_1 @ X0 @ X2) @ X1))),
% 0.88/1.06      inference('sup-', [status(thm)], ['31', '32'])).
% 0.88/1.06  thf('34', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_C))),
% 0.88/1.06      inference('sup-', [status(thm)], ['26', '33'])).
% 0.88/1.06  thf(t147_funct_1, axiom,
% 0.88/1.06    (![A:$i,B:$i]:
% 0.88/1.06     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.88/1.06       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.88/1.06         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.88/1.06  thf('35', plain,
% 0.88/1.06      (![X24 : $i, X25 : $i]:
% 0.88/1.06         (~ (r1_tarski @ X24 @ (k2_relat_1 @ X25))
% 0.88/1.06          | ((k9_relat_1 @ X25 @ (k10_relat_1 @ X25 @ X24)) = (X24))
% 0.88/1.06          | ~ (v1_funct_1 @ X25)
% 0.88/1.06          | ~ (v1_relat_1 @ X25))),
% 0.88/1.06      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.88/1.06  thf('36', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (~ (v1_relat_1 @ sk_C)
% 0.88/1.06          | ~ (v1_funct_1 @ sk_C)
% 0.88/1.06          | ((k9_relat_1 @ sk_C @ 
% 0.88/1.06              (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 0.88/1.06              = (k6_subset_1 @ sk_A @ X0)))),
% 0.88/1.06      inference('sup-', [status(thm)], ['34', '35'])).
% 0.88/1.06  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('39', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 0.88/1.06           = (k6_subset_1 @ sk_A @ X0))),
% 0.88/1.06      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.88/1.06  thf('40', plain,
% 0.88/1.06      ((((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)))
% 0.88/1.06          = (k6_subset_1 @ sk_A @ sk_A))
% 0.88/1.06        | ~ (v1_funct_1 @ sk_C)
% 0.88/1.06        | ~ (v1_relat_1 @ sk_C))),
% 0.88/1.06      inference('sup+', [status(thm)], ['25', '39'])).
% 0.88/1.06  thf('41', plain,
% 0.88/1.06      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.88/1.06         (((k10_relat_1 @ X21 @ (k6_subset_1 @ X22 @ X23))
% 0.88/1.06            = (k6_subset_1 @ (k10_relat_1 @ X21 @ X22) @ 
% 0.88/1.06               (k10_relat_1 @ X21 @ X23)))
% 0.88/1.06          | ~ (v1_funct_1 @ X21)
% 0.88/1.06          | ~ (v1_relat_1 @ X21))),
% 0.88/1.06      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.88/1.06  thf('42', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.88/1.06      inference('sup-', [status(thm)], ['5', '6'])).
% 0.88/1.06  thf('43', plain,
% 0.88/1.06      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf(t1_xboole_1, axiom,
% 0.88/1.06    (![A:$i,B:$i,C:$i]:
% 0.88/1.06     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.88/1.06       ( r1_tarski @ A @ C ) ))).
% 0.88/1.06  thf('44', plain,
% 0.88/1.06      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.88/1.06         (~ (r1_tarski @ X8 @ X9)
% 0.88/1.06          | ~ (r1_tarski @ X9 @ X10)
% 0.88/1.06          | (r1_tarski @ X8 @ X10))),
% 0.88/1.06      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.88/1.06  thf('45', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ X0)
% 0.88/1.06          | ~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_B) @ X0))),
% 0.88/1.06      inference('sup-', [status(thm)], ['43', '44'])).
% 0.88/1.06  thf('46', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.88/1.06          (k2_xboole_0 @ (k10_relat_1 @ sk_C @ sk_B) @ X0))),
% 0.88/1.06      inference('sup-', [status(thm)], ['42', '45'])).
% 0.88/1.06  thf('47', plain,
% 0.88/1.06      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.88/1.06         ((r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X15)
% 0.88/1.06          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.88/1.06      inference('demod', [status(thm)], ['14', '15'])).
% 0.88/1.06  thf('48', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (r1_tarski @ 
% 0.88/1.06          (k6_subset_1 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.88/1.06           (k10_relat_1 @ sk_C @ sk_B)) @ 
% 0.88/1.06          X0)),
% 0.88/1.06      inference('sup-', [status(thm)], ['46', '47'])).
% 0.88/1.06  thf('49', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((r1_tarski @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) @ X0)
% 0.88/1.06          | ~ (v1_relat_1 @ sk_C)
% 0.88/1.06          | ~ (v1_funct_1 @ sk_C))),
% 0.88/1.06      inference('sup+', [status(thm)], ['41', '48'])).
% 0.88/1.06  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('51', plain, ((v1_funct_1 @ sk_C)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('52', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (r1_tarski @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) @ X0)),
% 0.88/1.06      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.88/1.06  thf('53', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (r1_tarski @ (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)) @ X0)),
% 0.88/1.06      inference('sup-', [status(thm)], ['13', '16'])).
% 0.88/1.06  thf('54', plain,
% 0.88/1.06      (![X0 : $i, X2 : $i]:
% 0.88/1.06         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.88/1.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.88/1.06  thf('55', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (~ (r1_tarski @ X0 @ (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)))
% 0.88/1.06          | ((X0) = (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C))))),
% 0.88/1.06      inference('sup-', [status(thm)], ['53', '54'])).
% 0.88/1.06  thf('56', plain,
% 0.88/1.06      (((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B))
% 0.88/1.06         = (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)))),
% 0.88/1.06      inference('sup-', [status(thm)], ['52', '55'])).
% 0.88/1.06  thf('57', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 0.88/1.06           = (k6_subset_1 @ sk_A @ X0))),
% 0.88/1.06      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.88/1.06  thf('58', plain,
% 0.88/1.06      (((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_C)))
% 0.88/1.06         = (k6_subset_1 @ sk_A @ sk_B))),
% 0.88/1.06      inference('sup+', [status(thm)], ['56', '57'])).
% 0.88/1.06  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('61', plain,
% 0.88/1.06      (((k6_subset_1 @ sk_A @ sk_B) = (k6_subset_1 @ sk_A @ sk_A))),
% 0.88/1.06      inference('demod', [status(thm)], ['40', '58', '59', '60'])).
% 0.88/1.06  thf('62', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X1 @ X1) @ X0)),
% 0.88/1.06      inference('sup-', [status(thm)], ['18', '19'])).
% 0.88/1.06  thf('63', plain,
% 0.88/1.06      (![X0 : $i]: (r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ X0)),
% 0.88/1.06      inference('sup+', [status(thm)], ['61', '62'])).
% 0.88/1.06  thf(t44_xboole_1, axiom,
% 0.88/1.06    (![A:$i,B:$i,C:$i]:
% 0.88/1.06     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.88/1.06       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.88/1.06  thf('64', plain,
% 0.88/1.06      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.88/1.06         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 0.88/1.06          | ~ (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18))),
% 0.88/1.06      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.88/1.06  thf('65', plain,
% 0.88/1.06      (![X19 : $i, X20 : $i]:
% 0.88/1.06         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.88/1.06      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.88/1.06  thf('66', plain,
% 0.88/1.06      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.88/1.06         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 0.88/1.06          | ~ (r1_tarski @ (k6_subset_1 @ X16 @ X17) @ X18))),
% 0.88/1.06      inference('demod', [status(thm)], ['64', '65'])).
% 0.88/1.06  thf('67', plain,
% 0.88/1.06      (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ X0))),
% 0.88/1.06      inference('sup-', [status(thm)], ['63', '66'])).
% 0.88/1.06  thf('68', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.88/1.06      inference('sup+', [status(thm)], ['4', '67'])).
% 0.88/1.06  thf('69', plain, ($false), inference('demod', [status(thm)], ['0', '68'])).
% 0.88/1.06  
% 0.88/1.06  % SZS output end Refutation
% 0.88/1.06  
% 0.88/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

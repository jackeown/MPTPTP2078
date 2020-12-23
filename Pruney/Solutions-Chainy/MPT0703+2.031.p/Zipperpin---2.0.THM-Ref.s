%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GbrF7tJbSp

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:53 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 206 expanded)
%              Number of leaves         :   25 (  73 expanded)
%              Depth                    :   17
%              Number of atoms          :  689 (1730 expanded)
%              Number of equality atoms :   33 (  68 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k10_relat_1 @ X23 @ ( k6_subset_1 @ X24 @ X25 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X23 @ X24 ) @ ( k10_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
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

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k2_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      | ~ ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X12 @ X13 ) @ X14 )
      | ~ ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['1','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) ) @ X0 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('18',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','20'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('23',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X10 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('26',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X12 @ X13 ) @ X14 )
      | ~ ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('35',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X26 @ ( k2_relat_1 @ X27 ) )
      | ( ( k9_relat_1 @ X27 @ ( k10_relat_1 @ X27 @ X26 ) )
        = X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
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
    ( ( k9_relat_1 @ sk_C @ k1_xboole_0 )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['21','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('42',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X12 @ X13 ) @ X14 )
      | ~ ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','20'])).

thf('47',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k10_relat_1 @ X23 @ ( k6_subset_1 @ X24 @ X25 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X23 @ X24 ) @ ( k10_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ ( k6_subset_1 @ sk_A @ sk_B ) @ X0 ) )
        = ( k6_subset_1 @ k1_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X10 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ ( k6_subset_1 @ sk_A @ sk_B ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','51','52','53'])).

thf('55',plain,
    ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','54'])).

thf('56',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('57',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X26 @ ( k2_relat_1 @ X27 ) )
      | ( ( k9_relat_1 @ X27 @ ( k10_relat_1 @ X27 @ X26 ) )
        = X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k9_relat_1 @ sk_C @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k9_relat_1 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( k1_xboole_0
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','62'])).

thf('64',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('65',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('69',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('70',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ( r1_tarski @ ( k2_xboole_0 @ X18 @ X20 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('74',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['67','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['0','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GbrF7tJbSp
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:01:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.67/0.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.67/0.88  % Solved by: fo/fo7.sh
% 0.67/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.88  % done 1199 iterations in 0.428s
% 0.67/0.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.67/0.88  % SZS output start Refutation
% 0.67/0.88  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.67/0.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.67/0.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.67/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.88  thf(sk_C_type, type, sk_C: $i).
% 0.67/0.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.67/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.88  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.67/0.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.67/0.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.67/0.88  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.67/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.88  thf(t158_funct_1, conjecture,
% 0.67/0.88    (![A:$i,B:$i,C:$i]:
% 0.67/0.88     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.67/0.88       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.67/0.88           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.67/0.88         ( r1_tarski @ A @ B ) ) ))).
% 0.67/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.88    (~( ![A:$i,B:$i,C:$i]:
% 0.67/0.88        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.67/0.88          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.67/0.88              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.67/0.88            ( r1_tarski @ A @ B ) ) ) )),
% 0.67/0.88    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 0.67/0.88  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf(t138_funct_1, axiom,
% 0.67/0.88    (![A:$i,B:$i,C:$i]:
% 0.67/0.88     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.67/0.88       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.67/0.88         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.67/0.88  thf('1', plain,
% 0.67/0.88      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.67/0.88         (((k10_relat_1 @ X23 @ (k6_subset_1 @ X24 @ X25))
% 0.67/0.88            = (k6_subset_1 @ (k10_relat_1 @ X23 @ X24) @ 
% 0.67/0.88               (k10_relat_1 @ X23 @ X25)))
% 0.67/0.88          | ~ (v1_funct_1 @ X23)
% 0.67/0.88          | ~ (v1_relat_1 @ X23))),
% 0.67/0.88      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.67/0.88  thf(d10_xboole_0, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.67/0.88  thf('2', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.67/0.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.88  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.67/0.88      inference('simplify', [status(thm)], ['2'])).
% 0.67/0.88  thf(t11_xboole_1, axiom,
% 0.67/0.88    (![A:$i,B:$i,C:$i]:
% 0.67/0.88     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.67/0.88  thf('4', plain,
% 0.67/0.88      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.67/0.88         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.67/0.88      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.67/0.88  thf('5', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['3', '4'])).
% 0.67/0.88  thf('6', plain,
% 0.67/0.88      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf(t1_xboole_1, axiom,
% 0.67/0.88    (![A:$i,B:$i,C:$i]:
% 0.67/0.88     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.67/0.88       ( r1_tarski @ A @ C ) ))).
% 0.67/0.88  thf('7', plain,
% 0.67/0.88      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.67/0.88         (~ (r1_tarski @ X6 @ X7)
% 0.67/0.88          | ~ (r1_tarski @ X7 @ X8)
% 0.67/0.88          | (r1_tarski @ X6 @ X8))),
% 0.67/0.88      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.67/0.88  thf('8', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ X0)
% 0.67/0.88          | ~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_B) @ X0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['6', '7'])).
% 0.67/0.88  thf('9', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.67/0.88          (k2_xboole_0 @ (k10_relat_1 @ sk_C @ sk_B) @ X0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['5', '8'])).
% 0.67/0.88  thf(t43_xboole_1, axiom,
% 0.67/0.88    (![A:$i,B:$i,C:$i]:
% 0.67/0.88     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.67/0.88       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.67/0.88  thf('10', plain,
% 0.67/0.88      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.67/0.89         ((r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.67/0.89          | ~ (r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.67/0.89      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.67/0.89  thf(redefinition_k6_subset_1, axiom,
% 0.67/0.89    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.67/0.89  thf('11', plain,
% 0.67/0.89      (![X21 : $i, X22 : $i]:
% 0.67/0.89         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 0.67/0.89      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.67/0.89  thf('12', plain,
% 0.67/0.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.67/0.89         ((r1_tarski @ (k6_subset_1 @ X12 @ X13) @ X14)
% 0.67/0.89          | ~ (r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.67/0.89      inference('demod', [status(thm)], ['10', '11'])).
% 0.67/0.89  thf('13', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (r1_tarski @ 
% 0.67/0.89          (k6_subset_1 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.67/0.89           (k10_relat_1 @ sk_C @ sk_B)) @ 
% 0.67/0.89          X0)),
% 0.67/0.89      inference('sup-', [status(thm)], ['9', '12'])).
% 0.67/0.89  thf('14', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         ((r1_tarski @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) @ X0)
% 0.67/0.89          | ~ (v1_relat_1 @ sk_C)
% 0.67/0.89          | ~ (v1_funct_1 @ sk_C))),
% 0.67/0.89      inference('sup+', [status(thm)], ['1', '13'])).
% 0.67/0.89  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf('17', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (r1_tarski @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) @ X0)),
% 0.67/0.89      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.67/0.89  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.67/0.89  thf('18', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.67/0.89      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.67/0.89  thf('19', plain,
% 0.67/0.89      (![X0 : $i, X2 : $i]:
% 0.67/0.89         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.67/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.89  thf('20', plain,
% 0.67/0.89      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['18', '19'])).
% 0.67/0.89  thf('21', plain,
% 0.67/0.89      (((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.67/0.89      inference('sup-', [status(thm)], ['17', '20'])).
% 0.67/0.89  thf(t36_xboole_1, axiom,
% 0.67/0.89    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.67/0.89  thf('22', plain,
% 0.67/0.89      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.67/0.89      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.67/0.89  thf('23', plain,
% 0.67/0.89      (![X21 : $i, X22 : $i]:
% 0.67/0.89         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 0.67/0.89      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.67/0.89  thf('24', plain,
% 0.67/0.89      (![X10 : $i, X11 : $i]: (r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X10)),
% 0.67/0.89      inference('demod', [status(thm)], ['22', '23'])).
% 0.67/0.89  thf(t44_xboole_1, axiom,
% 0.67/0.89    (![A:$i,B:$i,C:$i]:
% 0.67/0.89     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.67/0.89       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.67/0.89  thf('25', plain,
% 0.67/0.89      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.67/0.89         ((r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 0.67/0.89          | ~ (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17))),
% 0.67/0.89      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.67/0.89  thf('26', plain,
% 0.67/0.89      (![X21 : $i, X22 : $i]:
% 0.67/0.89         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 0.67/0.89      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.67/0.89  thf('27', plain,
% 0.67/0.89      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.67/0.89         ((r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 0.67/0.89          | ~ (r1_tarski @ (k6_subset_1 @ X15 @ X16) @ X17))),
% 0.67/0.89      inference('demod', [status(thm)], ['25', '26'])).
% 0.67/0.89  thf('28', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.67/0.89      inference('sup-', [status(thm)], ['24', '27'])).
% 0.67/0.89  thf('29', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf('30', plain,
% 0.67/0.89      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.67/0.89         (~ (r1_tarski @ X6 @ X7)
% 0.67/0.89          | ~ (r1_tarski @ X7 @ X8)
% 0.67/0.89          | (r1_tarski @ X6 @ X8))),
% 0.67/0.89      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.67/0.89  thf('31', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0))),
% 0.67/0.89      inference('sup-', [status(thm)], ['29', '30'])).
% 0.67/0.89  thf('32', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_C)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['28', '31'])).
% 0.67/0.89  thf('33', plain,
% 0.67/0.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.67/0.89         ((r1_tarski @ (k6_subset_1 @ X12 @ X13) @ X14)
% 0.67/0.89          | ~ (r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.67/0.89      inference('demod', [status(thm)], ['10', '11'])).
% 0.67/0.89  thf('34', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_C))),
% 0.67/0.89      inference('sup-', [status(thm)], ['32', '33'])).
% 0.67/0.89  thf(t147_funct_1, axiom,
% 0.67/0.89    (![A:$i,B:$i]:
% 0.67/0.89     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.67/0.89       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.67/0.89         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.67/0.89  thf('35', plain,
% 0.67/0.89      (![X26 : $i, X27 : $i]:
% 0.67/0.89         (~ (r1_tarski @ X26 @ (k2_relat_1 @ X27))
% 0.67/0.89          | ((k9_relat_1 @ X27 @ (k10_relat_1 @ X27 @ X26)) = (X26))
% 0.67/0.89          | ~ (v1_funct_1 @ X27)
% 0.67/0.89          | ~ (v1_relat_1 @ X27))),
% 0.67/0.89      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.67/0.89  thf('36', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (~ (v1_relat_1 @ sk_C)
% 0.67/0.89          | ~ (v1_funct_1 @ sk_C)
% 0.67/0.89          | ((k9_relat_1 @ sk_C @ 
% 0.67/0.89              (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 0.67/0.89              = (k6_subset_1 @ sk_A @ X0)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['34', '35'])).
% 0.67/0.89  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf('39', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 0.67/0.89           = (k6_subset_1 @ sk_A @ X0))),
% 0.67/0.89      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.67/0.89  thf('40', plain,
% 0.67/0.89      (((k9_relat_1 @ sk_C @ k1_xboole_0) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.67/0.89      inference('sup+', [status(thm)], ['21', '39'])).
% 0.67/0.89  thf('41', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.67/0.89      inference('sup-', [status(thm)], ['3', '4'])).
% 0.67/0.89  thf('42', plain,
% 0.67/0.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.67/0.89         ((r1_tarski @ (k6_subset_1 @ X12 @ X13) @ X14)
% 0.67/0.89          | ~ (r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.67/0.89      inference('demod', [status(thm)], ['10', '11'])).
% 0.67/0.89  thf('43', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X1 @ X1) @ X0)),
% 0.67/0.89      inference('sup-', [status(thm)], ['41', '42'])).
% 0.67/0.89  thf('44', plain,
% 0.67/0.89      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['18', '19'])).
% 0.67/0.89  thf('45', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.67/0.89      inference('sup-', [status(thm)], ['43', '44'])).
% 0.67/0.89  thf('46', plain,
% 0.67/0.89      (((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.67/0.89      inference('sup-', [status(thm)], ['17', '20'])).
% 0.67/0.89  thf('47', plain,
% 0.67/0.89      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.67/0.89         (((k10_relat_1 @ X23 @ (k6_subset_1 @ X24 @ X25))
% 0.67/0.89            = (k6_subset_1 @ (k10_relat_1 @ X23 @ X24) @ 
% 0.67/0.89               (k10_relat_1 @ X23 @ X25)))
% 0.67/0.89          | ~ (v1_funct_1 @ X23)
% 0.67/0.89          | ~ (v1_relat_1 @ X23))),
% 0.67/0.89      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.67/0.89  thf('48', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (((k10_relat_1 @ sk_C @ 
% 0.67/0.89            (k6_subset_1 @ (k6_subset_1 @ sk_A @ sk_B) @ X0))
% 0.67/0.89            = (k6_subset_1 @ k1_xboole_0 @ (k10_relat_1 @ sk_C @ X0)))
% 0.67/0.89          | ~ (v1_relat_1 @ sk_C)
% 0.67/0.89          | ~ (v1_funct_1 @ sk_C))),
% 0.67/0.89      inference('sup+', [status(thm)], ['46', '47'])).
% 0.67/0.89  thf('49', plain,
% 0.67/0.89      (![X10 : $i, X11 : $i]: (r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X10)),
% 0.67/0.89      inference('demod', [status(thm)], ['22', '23'])).
% 0.67/0.89  thf('50', plain,
% 0.67/0.89      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['18', '19'])).
% 0.67/0.89  thf('51', plain,
% 0.67/0.89      (![X0 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.67/0.89      inference('sup-', [status(thm)], ['49', '50'])).
% 0.67/0.89  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf('54', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         ((k10_relat_1 @ sk_C @ 
% 0.67/0.89           (k6_subset_1 @ (k6_subset_1 @ sk_A @ sk_B) @ X0)) = (k1_xboole_0))),
% 0.67/0.89      inference('demod', [status(thm)], ['48', '51', '52', '53'])).
% 0.67/0.89  thf('55', plain, (((k10_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.89      inference('sup+', [status(thm)], ['45', '54'])).
% 0.67/0.89  thf('56', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.67/0.89      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.67/0.89  thf('57', plain,
% 0.67/0.89      (![X26 : $i, X27 : $i]:
% 0.67/0.89         (~ (r1_tarski @ X26 @ (k2_relat_1 @ X27))
% 0.67/0.89          | ((k9_relat_1 @ X27 @ (k10_relat_1 @ X27 @ X26)) = (X26))
% 0.67/0.89          | ~ (v1_funct_1 @ X27)
% 0.67/0.89          | ~ (v1_relat_1 @ X27))),
% 0.67/0.89      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.67/0.89  thf('58', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (~ (v1_relat_1 @ X0)
% 0.67/0.89          | ~ (v1_funct_1 @ X0)
% 0.67/0.89          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ k1_xboole_0))
% 0.67/0.89              = (k1_xboole_0)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['56', '57'])).
% 0.67/0.89  thf('59', plain,
% 0.67/0.89      ((((k9_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))
% 0.67/0.89        | ~ (v1_funct_1 @ sk_C)
% 0.67/0.89        | ~ (v1_relat_1 @ sk_C))),
% 0.67/0.89      inference('sup+', [status(thm)], ['55', '58'])).
% 0.67/0.89  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf('62', plain, (((k9_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.89      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.67/0.89  thf('63', plain, (((k1_xboole_0) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.67/0.89      inference('demod', [status(thm)], ['40', '62'])).
% 0.67/0.89  thf('64', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.67/0.89      inference('simplify', [status(thm)], ['2'])).
% 0.67/0.89  thf('65', plain,
% 0.67/0.89      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.67/0.89         ((r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 0.67/0.89          | ~ (r1_tarski @ (k6_subset_1 @ X15 @ X16) @ X17))),
% 0.67/0.89      inference('demod', [status(thm)], ['25', '26'])).
% 0.67/0.89  thf('66', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]:
% 0.67/0.89         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k6_subset_1 @ X1 @ X0)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['64', '65'])).
% 0.67/0.89  thf('67', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.67/0.89      inference('sup+', [status(thm)], ['63', '66'])).
% 0.67/0.89  thf('68', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.67/0.89      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.67/0.89  thf('69', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.67/0.89      inference('simplify', [status(thm)], ['2'])).
% 0.67/0.89  thf(t8_xboole_1, axiom,
% 0.67/0.89    (![A:$i,B:$i,C:$i]:
% 0.67/0.89     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.67/0.89       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.67/0.89  thf('70', plain,
% 0.67/0.89      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.67/0.89         (~ (r1_tarski @ X18 @ X19)
% 0.67/0.89          | ~ (r1_tarski @ X20 @ X19)
% 0.67/0.89          | (r1_tarski @ (k2_xboole_0 @ X18 @ X20) @ X19))),
% 0.67/0.89      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.67/0.89  thf('71', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]:
% 0.67/0.89         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 0.67/0.89      inference('sup-', [status(thm)], ['69', '70'])).
% 0.67/0.89  thf('72', plain,
% 0.67/0.89      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 0.67/0.89      inference('sup-', [status(thm)], ['68', '71'])).
% 0.67/0.89  thf('73', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.67/0.89      inference('sup-', [status(thm)], ['3', '4'])).
% 0.67/0.89  thf('74', plain,
% 0.67/0.89      (![X0 : $i, X2 : $i]:
% 0.67/0.89         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.67/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.89  thf('75', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]:
% 0.67/0.89         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.67/0.89          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['73', '74'])).
% 0.67/0.89  thf('76', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.67/0.89      inference('sup-', [status(thm)], ['72', '75'])).
% 0.67/0.89  thf('77', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.67/0.89      inference('demod', [status(thm)], ['67', '76'])).
% 0.67/0.89  thf('78', plain, ($false), inference('demod', [status(thm)], ['0', '77'])).
% 0.67/0.89  
% 0.67/0.89  % SZS output end Refutation
% 0.67/0.89  
% 0.67/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

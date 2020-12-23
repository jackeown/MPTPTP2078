%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0703+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7g9d2jMrq5

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:59 EST 2020

% Result     : Theorem 15.55s
% Output     : Refutation 15.55s
% Verified   : 
% Statistics : Number of formulae       :   62 (  76 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  365 ( 569 expanded)
%              Number of equality atoms :   31 (  35 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_26_type,type,(
    sk_B_26: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_48_type,type,(
    sk_C_48: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_8_type,type,(
    sk_A_8: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t158_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k10_relat_1 @ ( C @ A ) @ ( k10_relat_1 @ ( C @ B ) ) ) )
          & ( r1_tarski @ ( A @ ( k2_relat_1 @ C ) ) ) )
       => ( r1_tarski @ ( A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k10_relat_1 @ ( C @ A ) @ ( k10_relat_1 @ ( C @ B ) ) ) )
            & ( r1_tarski @ ( A @ ( k2_relat_1 @ C ) ) ) )
         => ( r1_tarski @ ( A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t158_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( sk_A_8 @ sk_B_26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k10_relat_1 @ ( sk_C_48 @ sk_A_8 ) @ ( k10_relat_1 @ ( sk_C_48 @ sk_B_26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('2',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('3',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k6_subset_1 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,
    ( ( k6_subset_1 @ ( k10_relat_1 @ ( sk_C_48 @ sk_A_8 ) @ ( k10_relat_1 @ ( sk_C_48 @ sk_B_26 ) ) ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ ( C @ ( k6_subset_1 @ ( A @ B ) ) ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ ( C @ A ) @ ( k10_relat_1 @ ( C @ B ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X2763: $i,X2764: $i,X2765: $i] :
      ( ( ( k10_relat_1 @ ( X2763 @ ( k6_subset_1 @ ( X2764 @ X2765 ) ) ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ ( X2763 @ X2764 ) @ ( k10_relat_1 @ ( X2763 @ X2765 ) ) ) ) )
      | ~ ( v1_funct_1 @ X2763 )
      | ~ ( v1_relat_1 @ X2763 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('8',plain,
    ( ( ( k10_relat_1 @ ( sk_C_48 @ ( k6_subset_1 @ ( sk_A_8 @ sk_B_26 ) ) ) )
      = o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_48 )
    | ~ ( v1_funct_1 @ sk_C_48 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_C_48 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_C_48 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k10_relat_1 @ ( sk_C_48 @ ( k6_subset_1 @ ( sk_A_8 @ sk_B_26 ) ) ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ ( B @ A ) )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B @ A ) ) ) ) )).

thf('12',plain,(
    ! [X2360: $i,X2361: $i] :
      ( ( ( k10_relat_1 @ ( X2360 @ X2361 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X2360 @ X2361 ) )
      | ~ ( v1_relat_1 @ X2360 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('13',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('14',plain,(
    ! [X2360: $i,X2361: $i] :
      ( ( ( k10_relat_1 @ ( X2360 @ X2361 ) )
       != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X2360 @ X2361 ) )
      | ~ ( v1_relat_1 @ X2360 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_48 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_C_48 @ ( k6_subset_1 @ ( sk_A_8 @ sk_B_26 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C_48 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_C_48 @ ( k6_subset_1 @ ( sk_A_8 @ sk_B_26 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_C_48 @ ( k6_subset_1 @ ( sk_A_8 @ sk_B_26 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    r1_tarski @ ( sk_A_8 @ ( k2_relat_1 @ sk_C_48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_xboole_0 @ ( B @ C ) ) )
     => ( r1_xboole_0 @ ( A @ C ) ) ) )).

thf('20',plain,(
    ! [X310: $i,X311: $i,X312: $i] :
      ( ~ ( r1_tarski @ ( X310 @ X311 ) )
      | ~ ( r1_xboole_0 @ ( X311 @ X312 ) )
      | ( r1_xboole_0 @ ( X310 @ X312 ) ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_A_8 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_C_48 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_xboole_0 @ ( sk_A_8 @ ( k6_subset_1 @ ( sk_A_8 @ sk_B_26 ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k4_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('23',plain,(
    ! [X373: $i,X374: $i] :
      ( ( ( k4_xboole_0 @ ( X373 @ X374 ) )
        = X373 )
      | ~ ( r1_xboole_0 @ ( X373 @ X374 ) ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('24',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('25',plain,(
    ! [X373: $i,X374: $i] :
      ( ( ( k6_subset_1 @ ( X373 @ X374 ) )
        = X373 )
      | ~ ( r1_xboole_0 @ ( X373 @ X374 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k6_subset_1 @ ( sk_A_8 @ ( k6_subset_1 @ ( sk_A_8 @ sk_B_26 ) ) ) )
    = sk_A_8 ),
    inference('sup-',[status(thm)],['22','25'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k4_xboole_0 @ ( A @ B ) ) ) )
      = ( k3_xboole_0 @ ( A @ B ) ) ) )).

thf('27',plain,(
    ! [X266: $i,X267: $i] :
      ( ( k4_xboole_0 @ ( X266 @ ( k4_xboole_0 @ ( X266 @ X267 ) ) ) )
      = ( k3_xboole_0 @ ( X266 @ X267 ) ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('29',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('30',plain,(
    ! [X266: $i,X267: $i] :
      ( ( k6_subset_1 @ ( X266 @ ( k6_subset_1 @ ( X266 @ X267 ) ) ) )
      = ( k3_xboole_0 @ ( X266 @ X267 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,
    ( ( k3_xboole_0 @ ( sk_B_26 @ sk_A_8 ) )
    = sk_A_8 ),
    inference(demod,[status(thm)],['26','30','31'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('33',plain,(
    ! [X175: $i,X176: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X175 @ X176 ) @ X175 ) ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('34',plain,(
    r1_tarski @ ( sk_A_8 @ sk_B_26 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------

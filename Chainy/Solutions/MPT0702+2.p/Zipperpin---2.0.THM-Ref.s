%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0702+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WNnpAl1FhB

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:59 EST 2020

% Result     : Theorem 17.32s
% Output     : Refutation 17.32s
% Verified   : 
% Statistics : Number of formulae       :   70 (  88 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :  410 ( 681 expanded)
%              Number of equality atoms :   36 (  42 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_A_8_type,type,(
    sk_A_8: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_26_type,type,(
    sk_B_26: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_48_type,type,(
    sk_C_48: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t157_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ ( C @ A ) @ ( k9_relat_1 @ ( C @ B ) ) ) )
          & ( r1_tarski @ ( A @ ( k1_relat_1 @ C ) ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ ( A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k9_relat_1 @ ( C @ A ) @ ( k9_relat_1 @ ( C @ B ) ) ) )
            & ( r1_tarski @ ( A @ ( k1_relat_1 @ C ) ) )
            & ( v2_funct_1 @ C ) )
         => ( r1_tarski @ ( A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t157_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( sk_A_8 @ sk_B_26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k9_relat_1 @ ( sk_C_48 @ sk_A_8 ) @ ( k9_relat_1 @ ( sk_C_48 @ sk_B_26 ) ) ) ),
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
    ( ( k6_subset_1 @ ( k9_relat_1 @ ( sk_C_48 @ sk_A_8 ) @ ( k9_relat_1 @ ( sk_C_48 @ sk_B_26 ) ) ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t123_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ ( C @ ( k6_subset_1 @ ( A @ B ) ) ) )
          = ( k6_subset_1 @ ( k9_relat_1 @ ( C @ A ) @ ( k9_relat_1 @ ( C @ B ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X2748: $i,X2749: $i,X2750: $i] :
      ( ~ ( v2_funct_1 @ X2748 )
      | ( ( k9_relat_1 @ ( X2748 @ ( k6_subset_1 @ ( X2749 @ X2750 ) ) ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ ( X2748 @ X2749 ) @ ( k9_relat_1 @ ( X2748 @ X2750 ) ) ) ) )
      | ~ ( v1_funct_1 @ X2748 )
      | ~ ( v1_relat_1 @ X2748 ) ) ),
    inference(cnf,[status(esa)],[t123_funct_1])).

thf('8',plain,
    ( ( ( k9_relat_1 @ ( sk_C_48 @ ( k6_subset_1 @ ( sk_A_8 @ sk_B_26 ) ) ) )
      = o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_48 )
    | ~ ( v1_funct_1 @ sk_C_48 )
    | ~ ( v2_funct_1 @ sk_C_48 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_C_48 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_C_48 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v2_funct_1 @ sk_C_48 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k9_relat_1 @ ( sk_C_48 @ ( k6_subset_1 @ ( sk_A_8 @ sk_B_26 ) ) ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ ( B @ A ) )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B @ A ) ) ) ) )).

thf('13',plain,(
    ! [X2309: $i,X2310: $i] :
      ( ( ( k9_relat_1 @ ( X2309 @ X2310 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X2309 @ X2310 ) )
      | ~ ( v1_relat_1 @ X2309 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,(
    ! [X2309: $i,X2310: $i] :
      ( ( ( k9_relat_1 @ ( X2309 @ X2310 ) )
       != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X2309 @ X2310 ) )
      | ~ ( v1_relat_1 @ X2309 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_48 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_C_48 @ ( k6_subset_1 @ ( sk_A_8 @ sk_B_26 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C_48 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_C_48 @ ( k6_subset_1 @ ( sk_A_8 @ sk_B_26 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_C_48 @ ( k6_subset_1 @ ( sk_A_8 @ sk_B_26 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    r1_tarski @ ( sk_A_8 @ ( k1_relat_1 @ sk_C_48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_xboole_0 @ ( B @ C ) ) )
     => ( r1_xboole_0 @ ( A @ C ) ) ) )).

thf('21',plain,(
    ! [X310: $i,X311: $i,X312: $i] :
      ( ~ ( r1_tarski @ ( X310 @ X311 ) )
      | ~ ( r1_xboole_0 @ ( X311 @ X312 ) )
      | ( r1_xboole_0 @ ( X310 @ X312 ) ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_A_8 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_C_48 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_xboole_0 @ ( sk_A_8 @ ( k6_subset_1 @ ( sk_A_8 @ sk_B_26 ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('24',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('25',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('26',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k3_xboole_0 @ ( sk_A_8 @ ( k6_subset_1 @ ( sk_A_8 @ sk_B_26 ) ) ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['23','26'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('28',plain,(
    ! [X235: $i,X236: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( X235 @ X236 ) @ X235 ) ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('29',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('30',plain,(
    ! [X235: $i,X236: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( X235 @ X236 ) @ X235 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('31',plain,(
    ! [X210: $i,X211: $i] :
      ( ( ( k3_xboole_0 @ ( X210 @ X211 ) )
        = X210 )
      | ~ ( r1_tarski @ ( X210 @ X211 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_subset_1 @ ( X0 @ X1 ) @ X0 ) )
      = ( k6_subset_1 @ ( X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( X0 @ ( k6_subset_1 @ ( X0 @ X1 ) ) ) )
      = ( k6_subset_1 @ ( X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k6_subset_1 @ ( sk_A_8 @ sk_B_26 ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X88: $i,X89: $i] :
      ( ( r1_tarski @ ( X88 @ X89 ) )
      | ( ( k4_xboole_0 @ ( X88 @ X89 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('37',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('38',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('39',plain,(
    ! [X88: $i,X89: $i] :
      ( ( r1_tarski @ ( X88 @ X89 ) )
      | ( ( k6_subset_1 @ ( X88 @ X89 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( r1_tarski @ ( sk_A_8 @ sk_B_26 ) ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    r1_tarski @ ( sk_A_8 @ sk_B_26 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['0','41'])).

%------------------------------------------------------------------------------

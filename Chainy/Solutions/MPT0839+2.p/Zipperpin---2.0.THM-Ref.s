%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0839+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HexSUmdG6J

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:02 EST 2020

% Result     : Theorem 34.92s
% Output     : Refutation 34.92s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 197 expanded)
%              Number of leaves         :   55 (  81 expanded)
%              Depth                    :   23
%              Number of atoms          :  872 (1545 expanded)
%              Number of equality atoms :   53 (  80 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_91_type,type,(
    sk_C_91: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_57_type,type,(
    sk_B_57: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ ( A @ ( k1_relat_1 @ A ) ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X2300: $i] :
      ( ( ( k9_relat_1 @ ( X2300 @ ( k1_relat_1 @ X2300 ) ) )
        = ( k2_relat_1 @ X2300 ) )
      | ~ ( v1_relat_1 @ X2300 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X997: $i,X998: $i] :
      ( ~ ( v1_xboole_0 @ X997 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( X997 @ X998 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf(t96_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ ( B @ A ) )
        = ( k3_xboole_0 @ ( B @ ( k2_zfmisc_1 @ ( A @ ( k2_relat_1 @ B ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X2609: $i,X2610: $i] :
      ( ( ( k7_relat_1 @ ( X2609 @ X2610 ) )
        = ( k3_xboole_0 @ ( X2609 @ ( k2_zfmisc_1 @ ( X2610 @ ( k2_relat_1 @ X2609 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ X2609 ) ) ),
    inference(cnf,[status(esa)],[t96_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ A ) )
         => ( r2_hidden @ ( C @ B ) ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ ( X14 @ X16 ) )
      | ( r2_hidden @ ( sk_C @ ( X16 @ X14 ) @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( X10 @ X11 ) )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t50_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( B @ A ) ) ) ) )
             => ~ ( ( ( k2_relset_1 @ ( B @ ( A @ C ) ) )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ ( D @ B ) )
                     => ~ ( r2_hidden @ ( D @ ( k1_relset_1 @ ( B @ ( A @ C ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( B @ A ) ) ) ) )
               => ~ ( ( ( k2_relset_1 @ ( B @ ( A @ C ) ) )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ ( D @ B ) )
                       => ~ ( r2_hidden @ ( D @ ( k1_relset_1 @ ( B @ ( A @ C ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_relset_1])).

thf('6',plain,(
    m1_subset_1 @ ( sk_C_91 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_A_14 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( A @ ( k1_zfmisc_1 @ B ) ) )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('7',plain,(
    ! [X1964: $i,X1965: $i] :
      ( ( r1_tarski @ ( X1964 @ X1965 ) )
      | ~ ( m1_subset_1 @ ( X1964 @ ( k1_zfmisc_1 @ X1965 ) ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ ( sk_C_91 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_A_14 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('9',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('10',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('11',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k4_xboole_0 @ ( sk_C_91 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_A_14 ) ) ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['8','11'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('13',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,
    ( ( k6_subset_1 @ ( sk_C_91 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_A_14 ) ) ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['12','13'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) )
     => ( ( r1_tarski @ ( A @ B ) )
        & ( r1_xboole_0 @ ( A @ C ) ) ) ) )).

thf('15',plain,(
    ! [X118: $i,X119: $i,X120: $i] :
      ( ( r1_xboole_0 @ ( X118 @ X120 ) )
      | ~ ( r1_tarski @ ( X118 @ ( k4_xboole_0 @ ( X119 @ X120 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('16',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ! [X118: $i,X119: $i,X120: $i] :
      ( ( r1_xboole_0 @ ( X118 @ X120 ) )
      | ~ ( r1_tarski @ ( X118 @ ( k6_subset_1 @ ( X119 @ X120 ) ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( X0 @ o_0_0_xboole_0 ) )
      | ( r1_xboole_0 @ ( X0 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_A_14 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( X0 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_A_14 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,(
    r1_tarski @ ( sk_C_91 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_A_14 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('21',plain,(
    ! [X161: $i,X162: $i] :
      ( ( ( k2_xboole_0 @ ( X162 @ X161 ) )
        = X161 )
      | ~ ( r1_tarski @ ( X162 @ X161 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('22',plain,
    ( ( k2_xboole_0 @ ( sk_C_91 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_A_14 ) ) ) )
    = ( k2_zfmisc_1 @ ( sk_B_57 @ sk_A_14 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ ( A @ B ) )
              & ( r1_xboole_0 @ ( A @ C ) ) )
          & ( r1_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) )
      & ~ ( ~ ( r1_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) )
          & ( r1_xboole_0 @ ( A @ B ) )
          & ( r1_xboole_0 @ ( A @ C ) ) ) ) )).

thf('23',plain,(
    ! [X331: $i,X332: $i,X334: $i] :
      ( ( r1_xboole_0 @ ( X331 @ X332 ) )
      | ~ ( r1_xboole_0 @ ( X331 @ ( k2_xboole_0 @ ( X332 @ X334 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( X0 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_A_14 ) ) ) )
      | ( r1_xboole_0 @ ( X0 @ sk_C_91 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( X0 @ sk_C_91 ) ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
     => ( r1_xboole_0 @ ( B @ A ) ) ) )).

thf('26',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( X47 @ X48 ) )
      | ~ ( r1_xboole_0 @ ( X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( sk_C_91 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k4_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('28',plain,(
    ! [X373: $i,X374: $i] :
      ( ( ( k4_xboole_0 @ ( X373 @ X374 ) )
        = X373 )
      | ~ ( r1_xboole_0 @ ( X373 @ X374 ) ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('29',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('30',plain,(
    ! [X373: $i,X374: $i] :
      ( ( ( k6_subset_1 @ ( X373 @ X374 ) )
        = X373 )
      | ~ ( r1_xboole_0 @ ( X373 @ X374 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_subset_1 @ ( sk_C_91 @ X0 ) )
        = sk_C_91 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf(t89_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( A @ B ) ) ) ) )).

thf('32',plain,(
    ! [X390: $i,X391: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( X390 @ X391 ) @ ( k4_xboole_0 @ ( X390 @ X391 ) ) ) ) ),
    inference(cnf,[status(esa)],[t89_xboole_1])).

thf('33',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('34',plain,(
    ! [X390: $i,X391: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( X390 @ X391 ) @ ( k6_subset_1 @ ( X390 @ X391 ) ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ ( sk_C_91 @ X0 ) @ sk_C_91 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ ( B @ A ) )
          & ( r1_xboole_0 @ ( B @ A ) ) ) ) )).

thf('36',plain,(
    ! [X326: $i,X327: $i] :
      ( ~ ( r1_xboole_0 @ ( X326 @ X327 ) )
      | ~ ( r1_tarski @ ( X326 @ X327 ) )
      | ( v1_xboole_0 @ X326 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ ( sk_C_91 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ ( sk_C_91 @ X0 ) @ sk_C_91 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('38',plain,(
    ! [X175: $i,X176: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X175 @ X176 ) @ X175 ) ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ ( sk_C_91 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k7_relat_1 @ ( sk_C_91 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C_91 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( X0 @ ( k2_relat_1 @ sk_C_91 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['2','39'])).

thf('41',plain,(
    m1_subset_1 @ ( sk_C_91 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_A_14 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('42',plain,(
    ! [X2039: $i,X2040: $i] :
      ( ~ ( m1_subset_1 @ ( X2039 @ ( k1_zfmisc_1 @ X2040 ) ) )
      | ( v1_relat_1 @ X2039 )
      | ~ ( v1_relat_1 @ X2040 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_A_14 ) ) )
    | ( v1_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) )).

thf('44',plain,(
    ! [X2178: $i,X2179: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ ( X2178 @ X2179 ) ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('45',plain,(
    v1_relat_1 @ sk_C_91 ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k7_relat_1 @ ( sk_C_91 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( X0 @ ( k2_relat_1 @ sk_C_91 ) ) ) ) ) ),
    inference(demod,[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k7_relat_1 @ ( sk_C_91 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','46'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('48',plain,(
    ! [X46: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('49',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('50',plain,(
    ! [X46: $i] :
      ( ( X46 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k7_relat_1 @ ( sk_C_91 @ X0 ) )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ ( B @ A ) ) )
        = ( k9_relat_1 @ ( B @ A ) ) ) ) )).

thf('52',plain,(
    ! [X2303: $i,X2304: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( X2303 @ X2304 ) ) )
        = ( k9_relat_1 @ ( X2303 @ X2304 ) ) )
      | ~ ( v1_relat_1 @ X2303 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ o_0_0_xboole_0 )
        = ( k9_relat_1 @ ( sk_C_91 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ sk_C_91 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('54',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('55',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('56',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('57',plain,
    ( ( k2_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C_91 ),
    inference(demod,[status(thm)],['43','44'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0
        = ( k9_relat_1 @ ( sk_C_91 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','57','58'])).

thf('60',plain,
    ( ( o_0_0_xboole_0
      = ( k2_relat_1 @ sk_C_91 ) )
    | ~ ( v1_relat_1 @ sk_C_91 )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_91 ) ) ),
    inference('sup+',[status(thm)],['0','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C_91 ),
    inference(demod,[status(thm)],['43','44'])).

thf('62',plain,
    ( ( o_0_0_xboole_0
      = ( k2_relat_1 @ sk_C_91 ) )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_91 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X12: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ( r2_hidden @ ( sk_B @ X12 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('64',plain,(
    m1_subset_1 @ ( sk_C_91 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_A_14 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( v4_relat_1 @ ( C @ A ) )
        & ( v5_relat_1 @ ( C @ B ) ) ) ) )).

thf('65',plain,(
    ! [X3536: $i,X3537: $i,X3538: $i] :
      ( ( v4_relat_1 @ ( X3536 @ X3537 ) )
      | ~ ( m1_subset_1 @ ( X3536 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3537 @ X3538 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('66',plain,(
    v4_relat_1 @ ( sk_C_91 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ ( B @ A ) )
      <=> ( r1_tarski @ ( k1_relat_1 @ B @ A ) ) ) ) )).

thf('67',plain,(
    ! [X2085: $i,X2086: $i] :
      ( ~ ( v4_relat_1 @ ( X2085 @ X2086 ) )
      | ( r1_tarski @ ( k1_relat_1 @ X2085 @ X2086 ) )
      | ~ ( v1_relat_1 @ X2085 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_C_91 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_91 @ sk_B_57 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C_91 ),
    inference(demod,[status(thm)],['43','44'])).

thf('70',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_91 @ sk_B_57 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X1964: $i,X1966: $i] :
      ( ( m1_subset_1 @ ( X1964 @ ( k1_zfmisc_1 @ X1966 ) ) )
      | ~ ( r1_tarski @ ( X1964 @ X1966 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('72',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_91 @ ( k1_zfmisc_1 @ sk_B_57 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ ( A @ B ) )
        & ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ C ) ) ) )
     => ( m1_subset_1 @ ( A @ C ) ) ) )).

thf('73',plain,(
    ! [X1985: $i,X1986: $i,X1987: $i] :
      ( ~ ( r2_hidden @ ( X1985 @ X1986 ) )
      | ~ ( m1_subset_1 @ ( X1986 @ ( k1_zfmisc_1 @ X1987 ) ) )
      | ( m1_subset_1 @ ( X1985 @ X1987 ) ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( X0 @ sk_B_57 ) )
      | ~ ( r2_hidden @ ( X0 @ ( k1_relat_1 @ sk_C_91 ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X3709: $i] :
      ( ~ ( r2_hidden @ ( X3709 @ ( k1_relset_1 @ ( sk_B_57 @ ( sk_A_14 @ sk_C_91 ) ) ) ) )
      | ~ ( m1_subset_1 @ ( X3709 @ sk_B_57 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ ( sk_C_91 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_A_14 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( k1_relset_1 @ ( A @ ( B @ C ) ) )
        = ( k1_relat_1 @ C ) ) ) )).

thf('77',plain,(
    ! [X3579: $i,X3580: $i,X3581: $i] :
      ( ( ( k1_relset_1 @ ( X3580 @ ( X3581 @ X3579 ) ) )
        = ( k1_relat_1 @ X3579 ) )
      | ~ ( m1_subset_1 @ ( X3579 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3580 @ X3581 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('78',plain,
    ( ( k1_relset_1 @ ( sk_B_57 @ ( sk_A_14 @ sk_C_91 ) ) )
    = ( k1_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X3709: $i] :
      ( ~ ( r2_hidden @ ( X3709 @ ( k1_relat_1 @ sk_C_91 ) ) )
      | ~ ( m1_subset_1 @ ( X3709 @ sk_B_57 ) ) ) ),
    inference(demod,[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( X0 @ ( k1_relat_1 @ sk_C_91 ) ) ) ),
    inference(clc,[status(thm)],['74','79'])).

thf('81',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['63','80'])).

thf('82',plain,
    ( o_0_0_xboole_0
    = ( k2_relat_1 @ sk_C_91 ) ),
    inference(demod,[status(thm)],['62','81'])).

thf('83',plain,(
    ( k2_relset_1 @ ( sk_B_57 @ ( sk_A_14 @ sk_C_91 ) ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('85',plain,(
    ( k2_relset_1 @ ( sk_B_57 @ ( sk_A_14 @ sk_C_91 ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ ( sk_C_91 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_A_14 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( k2_relset_1 @ ( A @ ( B @ C ) ) )
        = ( k2_relat_1 @ C ) ) ) )).

thf('87',plain,(
    ! [X3582: $i,X3583: $i,X3584: $i] :
      ( ( ( k2_relset_1 @ ( X3583 @ ( X3584 @ X3582 ) ) )
        = ( k2_relat_1 @ X3582 ) )
      | ~ ( m1_subset_1 @ ( X3582 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3583 @ X3584 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('88',plain,
    ( ( k2_relset_1 @ ( sk_B_57 @ ( sk_A_14 @ sk_C_91 ) ) )
    = ( k2_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ( k2_relat_1 @ sk_C_91 )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['85','88'])).

thf('90',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['82','89'])).

%------------------------------------------------------------------------------

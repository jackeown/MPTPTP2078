%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0838+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8LjiW1APmD

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:02 EST 2020

% Result     : Theorem 35.46s
% Output     : Refutation 35.46s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 180 expanded)
%              Number of leaves         :   53 (  74 expanded)
%              Depth                    :   20
%              Number of atoms          :  819 (1400 expanded)
%              Number of equality atoms :   41 (  64 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_57_type,type,(
    sk_B_57: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf(sk_C_91_type,type,(
    sk_C_91: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X2150: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X2150 ) )
      | ~ ( v1_xboole_0 @ X2150 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X46: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    ! [X46: $i] :
      ( ( X46 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t49_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
             => ~ ( ( ( k1_relset_1 @ ( A @ ( B @ C ) ) )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ ( D @ B ) )
                     => ~ ( r2_hidden @ ( D @ ( k2_relset_1 @ ( A @ ( B @ C ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
               => ~ ( ( ( k1_relset_1 @ ( A @ ( B @ C ) ) )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ ( D @ B ) )
                       => ~ ( r2_hidden @ ( D @ ( k2_relset_1 @ ( A @ ( B @ C ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_relset_1])).

thf('5',plain,(
    ( k1_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_91 ) ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('7',plain,(
    ( k1_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_91 ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ ( sk_C_91 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( k1_relset_1 @ ( A @ ( B @ C ) ) )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X3579: $i,X3580: $i,X3581: $i] :
      ( ( ( k1_relset_1 @ ( X3580 @ ( X3581 @ X3579 ) ) )
        = ( k1_relat_1 @ X3579 ) )
      | ~ ( m1_subset_1 @ ( X3579 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3580 @ X3581 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_91 ) ) )
    = ( k1_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ( k1_relat_1 @ sk_C_91 )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ sk_C_91 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t126_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ ( k2_relat_1 @ A @ A ) )
        = A ) ) )).

thf('14',plain,(
    ! [X2251: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X2251 @ X2251 ) )
        = X2251 )
      | ~ ( v1_relat_1 @ X2251 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X995: $i,X996: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( X995 @ X996 ) ) )
      | ~ ( v1_xboole_0 @ X996 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf(t124_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ ( A @ B ) )
        = ( k3_xboole_0 @ ( B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B @ A ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X2247: $i,X2248: $i] :
      ( ( ( k8_relat_1 @ ( X2248 @ X2247 ) )
        = ( k3_xboole_0 @ ( X2247 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X2247 @ X2248 ) ) ) ) )
      | ~ ( v1_relat_1 @ X2247 ) ) ),
    inference(cnf,[status(esa)],[t124_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ A ) )
         => ( r2_hidden @ ( C @ B ) ) ) ) )).

thf('17',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ ( X14 @ X16 ) )
      | ( r2_hidden @ ( sk_C @ ( X16 @ X14 ) @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( X10 @ X11 ) )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ ( sk_C_91 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( A @ ( k1_zfmisc_1 @ B ) ) )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('21',plain,(
    ! [X1964: $i,X1965: $i] :
      ( ( r1_tarski @ ( X1964 @ X1965 ) )
      | ~ ( m1_subset_1 @ ( X1964 @ ( k1_zfmisc_1 @ X1965 ) ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    r1_tarski @ ( sk_C_91 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('23',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('25',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ ( sk_C_91 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['22','25'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('27',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('28',plain,
    ( ( k6_subset_1 @ ( sk_C_91 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['26','27'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) )
     => ( ( r1_tarski @ ( A @ B ) )
        & ( r1_xboole_0 @ ( A @ C ) ) ) ) )).

thf('29',plain,(
    ! [X118: $i,X119: $i,X120: $i] :
      ( ( r1_xboole_0 @ ( X118 @ X120 ) )
      | ~ ( r1_tarski @ ( X118 @ ( k4_xboole_0 @ ( X119 @ X120 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('30',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('31',plain,(
    ! [X118: $i,X119: $i,X120: $i] :
      ( ( r1_xboole_0 @ ( X118 @ X120 ) )
      | ~ ( r1_tarski @ ( X118 @ ( k6_subset_1 @ ( X119 @ X120 ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( X0 @ o_0_0_xboole_0 ) )
      | ( r1_xboole_0 @ ( X0 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( X0 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['19','32'])).

thf('34',plain,(
    r1_tarski @ ( sk_C_91 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('35',plain,(
    ! [X161: $i,X162: $i] :
      ( ( ( k2_xboole_0 @ ( X162 @ X161 ) )
        = X161 )
      | ~ ( r1_tarski @ ( X162 @ X161 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('36',plain,
    ( ( k2_xboole_0 @ ( sk_C_91 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) ) )
    = ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ ( A @ B ) )
              & ( r1_xboole_0 @ ( A @ C ) ) )
          & ( r1_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) )
      & ~ ( ~ ( r1_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) )
          & ( r1_xboole_0 @ ( A @ B ) )
          & ( r1_xboole_0 @ ( A @ C ) ) ) ) )).

thf('37',plain,(
    ! [X331: $i,X332: $i,X334: $i] :
      ( ( r1_xboole_0 @ ( X331 @ X332 ) )
      | ~ ( r1_xboole_0 @ ( X331 @ ( k2_xboole_0 @ ( X332 @ X334 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( X0 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) ) )
      | ( r1_xboole_0 @ ( X0 @ sk_C_91 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( X0 @ sk_C_91 ) ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
     => ( r1_xboole_0 @ ( B @ A ) ) ) )).

thf('40',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( X47 @ X48 ) )
      | ~ ( r1_xboole_0 @ ( X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( sk_C_91 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k4_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('42',plain,(
    ! [X373: $i,X374: $i] :
      ( ( ( k4_xboole_0 @ ( X373 @ X374 ) )
        = X373 )
      | ~ ( r1_xboole_0 @ ( X373 @ X374 ) ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('43',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('44',plain,(
    ! [X373: $i,X374: $i] :
      ( ( ( k6_subset_1 @ ( X373 @ X374 ) )
        = X373 )
      | ~ ( r1_xboole_0 @ ( X373 @ X374 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_subset_1 @ ( sk_C_91 @ X0 ) )
        = sk_C_91 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf(t89_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( A @ B ) ) ) ) )).

thf('46',plain,(
    ! [X390: $i,X391: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( X390 @ X391 ) @ ( k4_xboole_0 @ ( X390 @ X391 ) ) ) ) ),
    inference(cnf,[status(esa)],[t89_xboole_1])).

thf('47',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('48',plain,(
    ! [X390: $i,X391: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( X390 @ X391 ) @ ( k6_subset_1 @ ( X390 @ X391 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ ( sk_C_91 @ X0 ) @ sk_C_91 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ ( B @ A ) )
          & ( r1_xboole_0 @ ( B @ A ) ) ) ) )).

thf('50',plain,(
    ! [X326: $i,X327: $i] :
      ( ~ ( r1_xboole_0 @ ( X326 @ X327 ) )
      | ~ ( r1_tarski @ ( X326 @ X327 ) )
      | ( v1_xboole_0 @ X326 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ ( sk_C_91 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ ( sk_C_91 @ X0 ) @ sk_C_91 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('52',plain,(
    ! [X175: $i,X176: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X175 @ X176 ) @ X175 ) ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ ( sk_C_91 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k8_relat_1 @ ( X0 @ sk_C_91 ) ) )
      | ~ ( v1_relat_1 @ sk_C_91 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_91 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['16','53'])).

thf('55',plain,(
    m1_subset_1 @ ( sk_C_91 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('56',plain,(
    ! [X2039: $i,X2040: $i] :
      ( ~ ( m1_subset_1 @ ( X2039 @ ( k1_zfmisc_1 @ X2040 ) ) )
      | ( v1_relat_1 @ X2039 )
      | ~ ( v1_relat_1 @ X2040 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) )
    | ( v1_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) )).

thf('58',plain,(
    ! [X2178: $i,X2179: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ ( X2178 @ X2179 ) ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('59',plain,(
    v1_relat_1 @ sk_C_91 ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k8_relat_1 @ ( X0 @ sk_C_91 ) ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_91 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k8_relat_1 @ ( X0 @ sk_C_91 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_C_91 )
    | ~ ( v1_relat_1 @ sk_C_91 )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_91 ) ) ),
    inference('sup+',[status(thm)],['14','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C_91 ),
    inference(demod,[status(thm)],['57','58'])).

thf('64',plain,
    ( ( v1_xboole_0 @ sk_C_91 )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_91 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X12: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ( r2_hidden @ ( sk_B @ X12 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('66',plain,(
    m1_subset_1 @ ( sk_C_91 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( v4_relat_1 @ ( C @ A ) )
        & ( v5_relat_1 @ ( C @ B ) ) ) ) )).

thf('67',plain,(
    ! [X3536: $i,X3537: $i,X3538: $i] :
      ( ( v5_relat_1 @ ( X3536 @ X3538 ) )
      | ~ ( m1_subset_1 @ ( X3536 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3537 @ X3538 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('68',plain,(
    v5_relat_1 @ ( sk_C_91 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ ( B @ A ) )
      <=> ( r1_tarski @ ( k2_relat_1 @ B @ A ) ) ) ) )).

thf('69',plain,(
    ! [X2087: $i,X2088: $i] :
      ( ~ ( v5_relat_1 @ ( X2087 @ X2088 ) )
      | ( r1_tarski @ ( k2_relat_1 @ X2087 @ X2088 ) )
      | ~ ( v1_relat_1 @ X2087 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ sk_C_91 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_91 @ sk_B_57 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_C_91 ),
    inference(demod,[status(thm)],['57','58'])).

thf('72',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_91 @ sk_B_57 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X1964: $i,X1966: $i] :
      ( ( m1_subset_1 @ ( X1964 @ ( k1_zfmisc_1 @ X1966 ) ) )
      | ~ ( r1_tarski @ ( X1964 @ X1966 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('74',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_91 @ ( k1_zfmisc_1 @ sk_B_57 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ ( A @ B ) )
        & ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ C ) ) ) )
     => ( m1_subset_1 @ ( A @ C ) ) ) )).

thf('75',plain,(
    ! [X1985: $i,X1986: $i,X1987: $i] :
      ( ~ ( r2_hidden @ ( X1985 @ X1986 ) )
      | ~ ( m1_subset_1 @ ( X1986 @ ( k1_zfmisc_1 @ X1987 ) ) )
      | ( m1_subset_1 @ ( X1985 @ X1987 ) ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( X0 @ sk_B_57 ) )
      | ~ ( r2_hidden @ ( X0 @ ( k2_relat_1 @ sk_C_91 ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X3702: $i] :
      ( ~ ( r2_hidden @ ( X3702 @ ( k2_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_91 ) ) ) ) )
      | ~ ( m1_subset_1 @ ( X3702 @ sk_B_57 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ ( sk_C_91 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( k2_relset_1 @ ( A @ ( B @ C ) ) )
        = ( k2_relat_1 @ C ) ) ) )).

thf('79',plain,(
    ! [X3582: $i,X3583: $i,X3584: $i] :
      ( ( ( k2_relset_1 @ ( X3583 @ ( X3584 @ X3582 ) ) )
        = ( k2_relat_1 @ X3582 ) )
      | ~ ( m1_subset_1 @ ( X3582 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3583 @ X3584 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('80',plain,
    ( ( k2_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_91 ) ) )
    = ( k2_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X3702: $i] :
      ( ~ ( r2_hidden @ ( X3702 @ ( k2_relat_1 @ sk_C_91 ) ) )
      | ~ ( m1_subset_1 @ ( X3702 @ sk_B_57 ) ) ) ),
    inference(demod,[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( X0 @ ( k2_relat_1 @ sk_C_91 ) ) ) ),
    inference(clc,[status(thm)],['76','81'])).

thf('83',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['65','82'])).

thf('84',plain,(
    v1_xboole_0 @ sk_C_91 ),
    inference(demod,[status(thm)],['64','83'])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['13','84'])).

%------------------------------------------------------------------------------

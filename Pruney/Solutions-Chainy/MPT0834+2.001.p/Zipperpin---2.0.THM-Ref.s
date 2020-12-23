%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WYV6z8QDlP

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:37 EST 2020

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 160 expanded)
%              Number of leaves         :   32 (  58 expanded)
%              Depth                    :   15
%              Number of atoms          :  839 (1910 expanded)
%              Number of equality atoms :   51 ( 125 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X19: $i] :
      ( ( ( k10_relat_1 @ X19 @ ( k2_relat_1 @ X19 ) )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t38_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( ( k7_relset_1 @ A @ B @ C @ A )
            = ( k2_relset_1 @ A @ B @ C ) )
          & ( ( k8_relset_1 @ A @ B @ C @ B )
            = ( k1_relset_1 @ A @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_relset_1])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X32 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k2_relset_1 @ X39 @ X40 @ X38 )
        = ( k2_relat_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ~ ( v1_relat_1 @ X22 )
      | ( r1_tarski @ ( k10_relat_1 @ X22 @ X20 ) @ ( k10_relat_1 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_C ) ) @ ( k10_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['0','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('14',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['13','14'])).

thf('17',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['12','15','16'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X17 @ X18 ) @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['13','14'])).

thf('23',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('27',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k8_relset_1 @ X46 @ X47 @ X45 @ X48 )
        = ( k10_relat_1 @ X45 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X35 )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('31',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','28','31'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X11: $i] :
      ( ( ( k9_relat_1 @ X11 @ ( k1_relat_1 @ X11 ) )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('35',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X29 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('36',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('38',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('41',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k9_relat_1 @ X16 @ X14 ) @ ( k9_relat_1 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_C ) ) @ ( k9_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['33','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['13','14'])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['13','14'])).

thf('46',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X11: $i] :
      ( ( ( k9_relat_1 @ X11 @ ( k1_relat_1 @ X11 ) )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t147_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) )).

thf('48',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X12 @ X13 ) @ ( k9_relat_1 @ X12 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t147_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['13','14'])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('57',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k7_relset_1 @ X42 @ X43 @ X41 @ X44 )
        = ( k9_relat_1 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('60',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('62',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('66',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['64','65'])).

thf('67',plain,(
    ( k10_relat_1 @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['32','66'])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WYV6z8QDlP
% 0.16/0.36  % Computer   : n005.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 11:25:33 EST 2020
% 0.22/0.37  % CPUTime    : 
% 0.22/0.37  % Running portfolio for 600 s
% 0.22/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.22/0.37  % Number of cores: 8
% 0.22/0.37  % Python version: Python 3.6.8
% 0.22/0.37  % Running in FO mode
% 0.81/1.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.81/1.01  % Solved by: fo/fo7.sh
% 0.81/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.81/1.01  % done 894 iterations in 0.535s
% 0.81/1.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.81/1.01  % SZS output start Refutation
% 0.81/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.81/1.01  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.81/1.01  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.81/1.01  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.81/1.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.81/1.01  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.81/1.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.81/1.01  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.81/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.81/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.81/1.01  thf(sk_C_type, type, sk_C: $i).
% 0.81/1.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.81/1.01  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.81/1.01  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.81/1.01  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.81/1.01  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.81/1.01  thf(t169_relat_1, axiom,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( v1_relat_1 @ A ) =>
% 0.81/1.01       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.81/1.01  thf('0', plain,
% 0.81/1.01      (![X19 : $i]:
% 0.81/1.01         (((k10_relat_1 @ X19 @ (k2_relat_1 @ X19)) = (k1_relat_1 @ X19))
% 0.81/1.01          | ~ (v1_relat_1 @ X19))),
% 0.81/1.01      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.81/1.01  thf(t38_relset_1, conjecture,
% 0.81/1.01    (![A:$i,B:$i,C:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.81/1.01       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.81/1.01         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.81/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.81/1.01    (~( ![A:$i,B:$i,C:$i]:
% 0.81/1.01        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.81/1.01          ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.81/1.01            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) )),
% 0.81/1.01    inference('cnf.neg', [status(esa)], [t38_relset_1])).
% 0.81/1.01  thf('1', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf(dt_k2_relset_1, axiom,
% 0.81/1.01    (![A:$i,B:$i,C:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.81/1.01       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.81/1.01  thf('2', plain,
% 0.81/1.01      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.81/1.01         ((m1_subset_1 @ (k2_relset_1 @ X32 @ X33 @ X34) @ (k1_zfmisc_1 @ X33))
% 0.81/1.01          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.81/1.01      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.81/1.01  thf('3', plain,
% 0.81/1.01      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.81/1.01      inference('sup-', [status(thm)], ['1', '2'])).
% 0.81/1.01  thf('4', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf(redefinition_k2_relset_1, axiom,
% 0.81/1.01    (![A:$i,B:$i,C:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.81/1.01       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.81/1.01  thf('5', plain,
% 0.81/1.01      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.81/1.01         (((k2_relset_1 @ X39 @ X40 @ X38) = (k2_relat_1 @ X38))
% 0.81/1.01          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.81/1.01      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.81/1.01  thf('6', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.81/1.01      inference('sup-', [status(thm)], ['4', '5'])).
% 0.81/1.01  thf('7', plain, ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.81/1.01      inference('demod', [status(thm)], ['3', '6'])).
% 0.81/1.01  thf(t3_subset, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.81/1.01  thf('8', plain,
% 0.81/1.01      (![X6 : $i, X7 : $i]:
% 0.81/1.01         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.81/1.01      inference('cnf', [status(esa)], [t3_subset])).
% 0.81/1.01  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.81/1.01      inference('sup-', [status(thm)], ['7', '8'])).
% 0.81/1.01  thf(t178_relat_1, axiom,
% 0.81/1.01    (![A:$i,B:$i,C:$i]:
% 0.81/1.01     ( ( v1_relat_1 @ C ) =>
% 0.81/1.01       ( ( r1_tarski @ A @ B ) =>
% 0.81/1.01         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.81/1.01  thf('10', plain,
% 0.81/1.01      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.81/1.01         (~ (r1_tarski @ X20 @ X21)
% 0.81/1.01          | ~ (v1_relat_1 @ X22)
% 0.81/1.01          | (r1_tarski @ (k10_relat_1 @ X22 @ X20) @ (k10_relat_1 @ X22 @ X21)))),
% 0.81/1.01      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.81/1.01  thf('11', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((r1_tarski @ (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_C)) @ 
% 0.81/1.01           (k10_relat_1 @ X0 @ sk_B))
% 0.81/1.01          | ~ (v1_relat_1 @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['9', '10'])).
% 0.81/1.01  thf('12', plain,
% 0.81/1.01      (((r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ sk_B))
% 0.81/1.01        | ~ (v1_relat_1 @ sk_C)
% 0.81/1.01        | ~ (v1_relat_1 @ sk_C))),
% 0.81/1.01      inference('sup+', [status(thm)], ['0', '11'])).
% 0.81/1.01  thf('13', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf(cc1_relset_1, axiom,
% 0.81/1.01    (![A:$i,B:$i,C:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.81/1.01       ( v1_relat_1 @ C ) ))).
% 0.81/1.01  thf('14', plain,
% 0.81/1.01      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.81/1.01         ((v1_relat_1 @ X26)
% 0.81/1.01          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.81/1.01      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.81/1.01  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.81/1.01      inference('sup-', [status(thm)], ['13', '14'])).
% 0.81/1.01  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 0.81/1.01      inference('sup-', [status(thm)], ['13', '14'])).
% 0.81/1.01  thf('17', plain,
% 0.81/1.01      ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.81/1.01      inference('demod', [status(thm)], ['12', '15', '16'])).
% 0.81/1.01  thf(t167_relat_1, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( v1_relat_1 @ B ) =>
% 0.81/1.01       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.81/1.01  thf('18', plain,
% 0.81/1.01      (![X17 : $i, X18 : $i]:
% 0.81/1.01         ((r1_tarski @ (k10_relat_1 @ X17 @ X18) @ (k1_relat_1 @ X17))
% 0.81/1.01          | ~ (v1_relat_1 @ X17))),
% 0.81/1.01      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.81/1.01  thf(d10_xboole_0, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.81/1.01  thf('19', plain,
% 0.81/1.01      (![X0 : $i, X2 : $i]:
% 0.81/1.01         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.81/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.81/1.01  thf('20', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         (~ (v1_relat_1 @ X0)
% 0.81/1.01          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.81/1.01          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['18', '19'])).
% 0.81/1.01  thf('21', plain,
% 0.81/1.01      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))
% 0.81/1.01        | ~ (v1_relat_1 @ sk_C))),
% 0.81/1.01      inference('sup-', [status(thm)], ['17', '20'])).
% 0.81/1.01  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.81/1.01      inference('sup-', [status(thm)], ['13', '14'])).
% 0.81/1.01  thf('23', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))),
% 0.81/1.01      inference('demod', [status(thm)], ['21', '22'])).
% 0.81/1.01  thf('24', plain,
% 0.81/1.01      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.81/1.01          != (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.81/1.01        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.81/1.01            != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('25', plain,
% 0.81/1.01      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.81/1.01          != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.81/1.01         <= (~
% 0.81/1.01             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.81/1.01                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.81/1.01      inference('split', [status(esa)], ['24'])).
% 0.81/1.01  thf('26', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf(redefinition_k8_relset_1, axiom,
% 0.81/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.81/1.01       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.81/1.01  thf('27', plain,
% 0.81/1.01      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.81/1.01         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 0.81/1.01          | ((k8_relset_1 @ X46 @ X47 @ X45 @ X48) = (k10_relat_1 @ X45 @ X48)))),
% 0.81/1.01      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.81/1.01  thf('28', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['26', '27'])).
% 0.81/1.01  thf('29', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf(redefinition_k1_relset_1, axiom,
% 0.81/1.01    (![A:$i,B:$i,C:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.81/1.01       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.81/1.01  thf('30', plain,
% 0.81/1.01      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.81/1.01         (((k1_relset_1 @ X36 @ X37 @ X35) = (k1_relat_1 @ X35))
% 0.81/1.01          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.81/1.01      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.81/1.01  thf('31', plain,
% 0.81/1.01      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.81/1.01      inference('sup-', [status(thm)], ['29', '30'])).
% 0.81/1.01  thf('32', plain,
% 0.81/1.01      ((((k10_relat_1 @ sk_C @ sk_B) != (k1_relat_1 @ sk_C)))
% 0.81/1.01         <= (~
% 0.81/1.01             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.81/1.01                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.81/1.01      inference('demod', [status(thm)], ['25', '28', '31'])).
% 0.81/1.01  thf(t146_relat_1, axiom,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( v1_relat_1 @ A ) =>
% 0.81/1.01       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.81/1.01  thf('33', plain,
% 0.81/1.01      (![X11 : $i]:
% 0.81/1.01         (((k9_relat_1 @ X11 @ (k1_relat_1 @ X11)) = (k2_relat_1 @ X11))
% 0.81/1.01          | ~ (v1_relat_1 @ X11))),
% 0.81/1.01      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.81/1.01  thf('34', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf(dt_k1_relset_1, axiom,
% 0.81/1.01    (![A:$i,B:$i,C:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.81/1.01       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.81/1.01  thf('35', plain,
% 0.81/1.01      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.81/1.01         ((m1_subset_1 @ (k1_relset_1 @ X29 @ X30 @ X31) @ (k1_zfmisc_1 @ X29))
% 0.81/1.01          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.81/1.01      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.81/1.01  thf('36', plain,
% 0.81/1.01      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.81/1.01      inference('sup-', [status(thm)], ['34', '35'])).
% 0.81/1.01  thf('37', plain,
% 0.81/1.01      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.81/1.01      inference('sup-', [status(thm)], ['29', '30'])).
% 0.81/1.01  thf('38', plain,
% 0.81/1.01      ((m1_subset_1 @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.81/1.01      inference('demod', [status(thm)], ['36', '37'])).
% 0.81/1.01  thf('39', plain,
% 0.81/1.01      (![X6 : $i, X7 : $i]:
% 0.81/1.01         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.81/1.01      inference('cnf', [status(esa)], [t3_subset])).
% 0.81/1.01  thf('40', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.81/1.01      inference('sup-', [status(thm)], ['38', '39'])).
% 0.81/1.01  thf(t156_relat_1, axiom,
% 0.81/1.01    (![A:$i,B:$i,C:$i]:
% 0.81/1.01     ( ( v1_relat_1 @ C ) =>
% 0.81/1.01       ( ( r1_tarski @ A @ B ) =>
% 0.81/1.01         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.81/1.01  thf('41', plain,
% 0.81/1.01      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.81/1.01         (~ (r1_tarski @ X14 @ X15)
% 0.81/1.01          | ~ (v1_relat_1 @ X16)
% 0.81/1.01          | (r1_tarski @ (k9_relat_1 @ X16 @ X14) @ (k9_relat_1 @ X16 @ X15)))),
% 0.81/1.01      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.81/1.01  thf('42', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_C)) @ 
% 0.81/1.01           (k9_relat_1 @ X0 @ sk_A))
% 0.81/1.01          | ~ (v1_relat_1 @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['40', '41'])).
% 0.81/1.01  thf('43', plain,
% 0.81/1.01      (((r1_tarski @ (k2_relat_1 @ sk_C) @ (k9_relat_1 @ sk_C @ sk_A))
% 0.81/1.01        | ~ (v1_relat_1 @ sk_C)
% 0.81/1.01        | ~ (v1_relat_1 @ sk_C))),
% 0.81/1.01      inference('sup+', [status(thm)], ['33', '42'])).
% 0.81/1.01  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.81/1.01      inference('sup-', [status(thm)], ['13', '14'])).
% 0.81/1.01  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.81/1.01      inference('sup-', [status(thm)], ['13', '14'])).
% 0.81/1.01  thf('46', plain,
% 0.81/1.01      ((r1_tarski @ (k2_relat_1 @ sk_C) @ (k9_relat_1 @ sk_C @ sk_A))),
% 0.81/1.01      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.81/1.01  thf('47', plain,
% 0.81/1.01      (![X11 : $i]:
% 0.81/1.01         (((k9_relat_1 @ X11 @ (k1_relat_1 @ X11)) = (k2_relat_1 @ X11))
% 0.81/1.01          | ~ (v1_relat_1 @ X11))),
% 0.81/1.01      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.81/1.01  thf(t147_relat_1, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( v1_relat_1 @ B ) =>
% 0.81/1.01       ( r1_tarski @
% 0.81/1.01         ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ))).
% 0.81/1.01  thf('48', plain,
% 0.81/1.01      (![X12 : $i, X13 : $i]:
% 0.81/1.01         ((r1_tarski @ (k9_relat_1 @ X12 @ X13) @ 
% 0.81/1.01           (k9_relat_1 @ X12 @ (k1_relat_1 @ X12)))
% 0.81/1.01          | ~ (v1_relat_1 @ X12))),
% 0.81/1.01      inference('cnf', [status(esa)], [t147_relat_1])).
% 0.81/1.01  thf('49', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0))
% 0.81/1.01          | ~ (v1_relat_1 @ X0)
% 0.81/1.01          | ~ (v1_relat_1 @ X0))),
% 0.81/1.01      inference('sup+', [status(thm)], ['47', '48'])).
% 0.81/1.01  thf('50', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         (~ (v1_relat_1 @ X0)
% 0.81/1.01          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0)))),
% 0.81/1.01      inference('simplify', [status(thm)], ['49'])).
% 0.81/1.01  thf('51', plain,
% 0.81/1.01      (![X0 : $i, X2 : $i]:
% 0.81/1.01         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.81/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.81/1.01  thf('52', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         (~ (v1_relat_1 @ X0)
% 0.81/1.01          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k9_relat_1 @ X0 @ X1))
% 0.81/1.01          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['50', '51'])).
% 0.81/1.01  thf('53', plain,
% 0.81/1.01      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.81/1.01        | ~ (v1_relat_1 @ sk_C))),
% 0.81/1.01      inference('sup-', [status(thm)], ['46', '52'])).
% 0.81/1.01  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 0.81/1.01      inference('sup-', [status(thm)], ['13', '14'])).
% 0.81/1.01  thf('55', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.81/1.01      inference('demod', [status(thm)], ['53', '54'])).
% 0.81/1.01  thf('56', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf(redefinition_k7_relset_1, axiom,
% 0.81/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.81/1.01       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.81/1.01  thf('57', plain,
% 0.81/1.01      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.81/1.01         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.81/1.01          | ((k7_relset_1 @ X42 @ X43 @ X41 @ X44) = (k9_relat_1 @ X41 @ X44)))),
% 0.81/1.01      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.81/1.01  thf('58', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['56', '57'])).
% 0.81/1.01  thf('59', plain,
% 0.81/1.01      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.81/1.01          != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.81/1.01         <= (~
% 0.81/1.01             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.81/1.01                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.81/1.01      inference('split', [status(esa)], ['24'])).
% 0.81/1.01  thf('60', plain,
% 0.81/1.01      ((((k9_relat_1 @ sk_C @ sk_A) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.81/1.01         <= (~
% 0.81/1.01             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.81/1.01                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['58', '59'])).
% 0.81/1.01  thf('61', plain,
% 0.81/1.01      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.81/1.01      inference('sup-', [status(thm)], ['4', '5'])).
% 0.81/1.01  thf('62', plain,
% 0.81/1.01      ((((k9_relat_1 @ sk_C @ sk_A) != (k2_relat_1 @ sk_C)))
% 0.81/1.01         <= (~
% 0.81/1.01             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.81/1.01                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.81/1.01      inference('demod', [status(thm)], ['60', '61'])).
% 0.81/1.01  thf('63', plain,
% 0.81/1.01      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.81/1.01         <= (~
% 0.81/1.01             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.81/1.01                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['55', '62'])).
% 0.81/1.01  thf('64', plain,
% 0.81/1.01      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.81/1.01          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.81/1.01      inference('simplify', [status(thm)], ['63'])).
% 0.81/1.01  thf('65', plain,
% 0.81/1.01      (~
% 0.81/1.01       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.81/1.01          = (k1_relset_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.81/1.01       ~
% 0.81/1.01       (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.81/1.01          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.81/1.01      inference('split', [status(esa)], ['24'])).
% 0.81/1.01  thf('66', plain,
% 0.81/1.01      (~
% 0.81/1.01       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.81/1.01          = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.81/1.01      inference('sat_resolution*', [status(thm)], ['64', '65'])).
% 0.81/1.01  thf('67', plain, (((k10_relat_1 @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.81/1.01      inference('simpl_trail', [status(thm)], ['32', '66'])).
% 0.81/1.01  thf('68', plain, ($false),
% 0.81/1.01      inference('simplify_reflect-', [status(thm)], ['23', '67'])).
% 0.81/1.01  
% 0.81/1.01  % SZS output end Refutation
% 0.81/1.01  
% 0.81/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

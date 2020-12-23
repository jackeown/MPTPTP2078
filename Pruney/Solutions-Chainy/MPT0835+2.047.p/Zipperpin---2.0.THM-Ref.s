%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xxsuuvIVIr

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 222 expanded)
%              Number of leaves         :   26 (  73 expanded)
%              Depth                    :   17
%              Number of atoms          : 1206 (3148 expanded)
%              Number of equality atoms :   85 ( 197 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X23 )
      | ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k7_relset_1 @ X14 @ X15 @ X13 @ X16 )
        = ( k9_relat_1 @ X13 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('12',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k7_relset_1 @ X28 @ X29 @ X30 @ X28 )
        = ( k2_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t39_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
          = ( k2_relset_1 @ B @ A @ C ) )
        & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
          = ( k1_relset_1 @ B @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
       => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
            = ( k2_relset_1 @ B @ A @ C ) )
          & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
            = ( k1_relset_1 @ B @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_relset_1])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k8_relset_1 @ X28 @ X29 @ X30 @ X29 )
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('20',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( ( k8_relset_1 @ X18 @ X19 @ X17 @ X20 )
        = ( k10_relat_1 @ X17 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['20','23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k7_relset_1 @ X14 @ X15 @ X13 @ X16 )
        = ( k9_relat_1 @ X13 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('37',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('40',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('45',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( ( k8_relset_1 @ X18 @ X19 @ X17 @ X20 )
        = ( k10_relat_1 @ X17 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('48',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k8_relset_1 @ X28 @ X29 @ X30 @ X29 )
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k7_relset_1 @ X28 @ X29 @ X30 @ X28 )
        = ( k2_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('56',plain,
    ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B )
    = ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('58',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('59',plain,
    ( ( k9_relat_1 @ sk_C @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('62',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['32'])).

thf('63',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('65',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('70',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('72',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['68','73'])).

thf('75',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['32'])).

thf('77',plain,(
    ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
 != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['75','76'])).

thf('78',plain,(
    ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['40','77'])).

thf('79',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['71','72'])).

thf('81',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    $false ),
    inference(simplify,[status(thm)],['81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xxsuuvIVIr
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:20:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 58 iterations in 0.025s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.49  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.49  thf(d10_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.49  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.49      inference('simplify', [status(thm)], ['0'])).
% 0.22/0.49  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.49      inference('simplify', [status(thm)], ['0'])).
% 0.22/0.49  thf(t11_relset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ C ) =>
% 0.22/0.49       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.22/0.49           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.22/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.49         (~ (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 0.22/0.49          | ~ (r1_tarski @ (k2_relat_1 @ X21) @ X23)
% 0.22/0.49          | (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.22/0.49          | ~ (v1_relat_1 @ X21))),
% 0.22/0.49      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X0)
% 0.22/0.49          | (m1_subset_1 @ X0 @ 
% 0.22/0.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.22/0.49          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((m1_subset_1 @ X0 @ 
% 0.22/0.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.22/0.49          | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.49  thf(redefinition_k2_relset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.49         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.22/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X0)
% 0.22/0.49          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.22/0.49              = (k2_relat_1 @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((m1_subset_1 @ X0 @ 
% 0.22/0.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.22/0.49          | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.49  thf(redefinition_k7_relset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.49       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.22/0.49          | ((k7_relset_1 @ X14 @ X15 @ X13 @ X16) = (k9_relat_1 @ X13 @ X16)))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X0)
% 0.22/0.49          | ((k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1)
% 0.22/0.49              = (k9_relat_1 @ X0 @ X1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((m1_subset_1 @ X0 @ 
% 0.22/0.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.22/0.49          | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.49  thf(t38_relset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.49       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.22/0.49         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.22/0.49         (((k7_relset_1 @ X28 @ X29 @ X30 @ X28)
% 0.22/0.49            = (k2_relset_1 @ X28 @ X29 @ X30))
% 0.22/0.49          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.22/0.49      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X0)
% 0.22/0.49          | ((k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ 
% 0.22/0.49              (k1_relat_1 @ X0))
% 0.22/0.49              = (k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.22/0.49            = (k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0))
% 0.22/0.49          | ~ (v1_relat_1 @ X0)
% 0.22/0.49          | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['10', '13'])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X0)
% 0.22/0.49          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.22/0.49              = (k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['14'])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 0.22/0.49          | ~ (v1_relat_1 @ X0)
% 0.22/0.49          | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['7', '15'])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X0)
% 0.22/0.49          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.22/0.49  thf(t39_relset_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.49       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.22/0.49           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.22/0.49         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.22/0.49           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.49        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.49          ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.22/0.49              ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.22/0.49            ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.22/0.49              ( k1_relset_1 @ B @ A @ C ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t39_relset_1])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.22/0.49         (((k8_relset_1 @ X28 @ X29 @ X30 @ X29)
% 0.22/0.49            = (k1_relset_1 @ X28 @ X29 @ X30))
% 0.22/0.49          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.22/0.49      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.22/0.49         = (k1_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(redefinition_k8_relset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.49       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.22/0.49          | ((k8_relset_1 @ X18 @ X19 @ X17 @ X20) = (k10_relat_1 @ X17 @ X20)))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.22/0.49          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.49  thf('27', plain, (((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['20', '23', '26'])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.22/0.49          | ((k7_relset_1 @ X14 @ X15 @ X13 @ X16) = (k9_relat_1 @ X13 @ X16)))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.49          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.49          != (k2_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.22/0.49        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.49            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.49            != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.49          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.49          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.22/0.49         <= (~
% 0.22/0.49             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.49                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.49                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.49      inference('split', [status(esa)], ['32'])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      ((((k9_relat_1 @ sk_C @ (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.49          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.22/0.49         <= (~
% 0.22/0.49             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.49                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.49                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['31', '33'])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.49         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.22/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.49  thf('37', plain,
% 0.22/0.49      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      ((((k9_relat_1 @ sk_C @ (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.49          != (k2_relat_1 @ sk_C)))
% 0.22/0.49         <= (~
% 0.22/0.49             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.49                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.49                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.49      inference('demod', [status(thm)], ['34', '37'])).
% 0.22/0.49  thf('39', plain,
% 0.22/0.49      ((((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.22/0.49          != (k2_relat_1 @ sk_C)))
% 0.22/0.49         <= (~
% 0.22/0.49             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.49                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.49                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['28', '38'])).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      ((((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.22/0.49         <= (~
% 0.22/0.49             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.49                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.49                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['27', '39'])).
% 0.22/0.49  thf('41', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((m1_subset_1 @ X0 @ 
% 0.22/0.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.22/0.49          | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.49  thf('42', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.22/0.49          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.49  thf('43', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X0)
% 0.22/0.49          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.22/0.49              = (k1_relat_1 @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.49  thf('44', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((m1_subset_1 @ X0 @ 
% 0.22/0.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.22/0.49          | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.49  thf('45', plain,
% 0.22/0.49      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.22/0.49          | ((k8_relset_1 @ X18 @ X19 @ X17 @ X20) = (k10_relat_1 @ X17 @ X20)))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.22/0.49  thf('46', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X0)
% 0.22/0.49          | ((k8_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1)
% 0.22/0.49              = (k10_relat_1 @ X0 @ X1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.49  thf('47', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((m1_subset_1 @ X0 @ 
% 0.22/0.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.22/0.49          | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.49  thf('48', plain,
% 0.22/0.49      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.22/0.49         (((k8_relset_1 @ X28 @ X29 @ X30 @ X29)
% 0.22/0.49            = (k1_relset_1 @ X28 @ X29 @ X30))
% 0.22/0.49          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.22/0.49      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.22/0.49  thf('49', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X0)
% 0.22/0.49          | ((k8_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ 
% 0.22/0.49              (k2_relat_1 @ X0))
% 0.22/0.49              = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.22/0.49  thf('50', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0))
% 0.22/0.49            = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0))
% 0.22/0.49          | ~ (v1_relat_1 @ X0)
% 0.22/0.49          | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['46', '49'])).
% 0.22/0.49  thf('51', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X0)
% 0.22/0.49          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0))
% 0.22/0.49              = (k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['50'])).
% 0.22/0.49  thf('52', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.22/0.49          | ~ (v1_relat_1 @ X0)
% 0.22/0.49          | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['43', '51'])).
% 0.22/0.49  thf('53', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X0)
% 0.22/0.49          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['52'])).
% 0.22/0.49  thf('54', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('55', plain,
% 0.22/0.49      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.22/0.49         (((k7_relset_1 @ X28 @ X29 @ X30 @ X28)
% 0.22/0.49            = (k2_relset_1 @ X28 @ X29 @ X30))
% 0.22/0.49          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.22/0.49      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.22/0.49  thf('56', plain,
% 0.22/0.49      (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 0.22/0.49         = (k2_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.49  thf('57', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.49  thf('58', plain,
% 0.22/0.49      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.49  thf('59', plain, (((k9_relat_1 @ sk_C @ sk_B) = (k2_relat_1 @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.22/0.49  thf('60', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.49  thf('61', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.49  thf('62', plain,
% 0.22/0.49      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.49          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.49          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.22/0.49         <= (~
% 0.22/0.49             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.49                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.49                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.49      inference('split', [status(esa)], ['32'])).
% 0.22/0.49  thf('63', plain,
% 0.22/0.49      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.22/0.49          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.22/0.49         <= (~
% 0.22/0.49             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.49                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.49                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['61', '62'])).
% 0.22/0.49  thf('64', plain,
% 0.22/0.49      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.49  thf('65', plain,
% 0.22/0.49      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.22/0.49          != (k1_relat_1 @ sk_C)))
% 0.22/0.49         <= (~
% 0.22/0.49             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.49                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.49                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.49      inference('demod', [status(thm)], ['63', '64'])).
% 0.22/0.49  thf('66', plain,
% 0.22/0.49      ((((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.22/0.49          != (k1_relat_1 @ sk_C)))
% 0.22/0.49         <= (~
% 0.22/0.49             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.49                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.49                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['60', '65'])).
% 0.22/0.49  thf('67', plain,
% 0.22/0.49      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.22/0.49         <= (~
% 0.22/0.49             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.49                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.49                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['59', '66'])).
% 0.22/0.49  thf('68', plain,
% 0.22/0.49      (((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C)))
% 0.22/0.49         <= (~
% 0.22/0.49             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.49                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.49                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['53', '67'])).
% 0.22/0.49  thf('69', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(cc2_relat_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.49  thf('70', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.22/0.49          | (v1_relat_1 @ X3)
% 0.22/0.49          | ~ (v1_relat_1 @ X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.49  thf('71', plain,
% 0.22/0.49      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['69', '70'])).
% 0.22/0.49  thf(fc6_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.49  thf('72', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.49  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.49      inference('demod', [status(thm)], ['71', '72'])).
% 0.22/0.49  thf('74', plain,
% 0.22/0.49      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 0.22/0.49         <= (~
% 0.22/0.49             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.49                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.49                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.49      inference('demod', [status(thm)], ['68', '73'])).
% 0.22/0.49  thf('75', plain,
% 0.22/0.49      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.49          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.49          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['74'])).
% 0.22/0.49  thf('76', plain,
% 0.22/0.49      (~
% 0.22/0.49       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.49          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.49          = (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.22/0.49       ~
% 0.22/0.49       (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.49          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.49          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.22/0.49      inference('split', [status(esa)], ['32'])).
% 0.22/0.49  thf('77', plain,
% 0.22/0.49      (~
% 0.22/0.49       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.49          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.49          = (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['75', '76'])).
% 0.22/0.49  thf('78', plain,
% 0.22/0.49      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['40', '77'])).
% 0.22/0.49  thf('79', plain,
% 0.22/0.49      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['17', '78'])).
% 0.22/0.49  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.49      inference('demod', [status(thm)], ['71', '72'])).
% 0.22/0.49  thf('81', plain, (((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['79', '80'])).
% 0.22/0.49  thf('82', plain, ($false), inference('simplify', [status(thm)], ['81'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

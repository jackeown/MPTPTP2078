%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Uugpchq4ie

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:45 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 370 expanded)
%              Number of leaves         :   37 ( 126 expanded)
%              Depth                    :   12
%              Number of atoms          :  932 (4725 expanded)
%              Number of equality atoms :   60 ( 251 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf('0',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('6',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('9',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k7_relset_1 @ X35 @ X36 @ X34 @ X37 )
        = ( k9_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('14',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14
        = ( k7_relat_1 @ X14 @ X15 ) )
      | ~ ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['16','19'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('22',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('24',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','10','11','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('27',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k8_relset_1 @ X39 @ X40 @ X38 @ X41 )
        = ( k10_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('32',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('36',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['34','35'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('37',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('38',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_A )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k10_relat_1 @ X12 @ X13 )
        = ( k10_relat_1 @ X12 @ ( k3_xboole_0 @ ( k2_relat_1 @ X12 ) @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('40',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('42',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k10_relat_1 @ sk_C @ sk_A )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','28','29','42'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['44'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('46',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( r1_tarski @ X16 @ ( k10_relat_1 @ X17 @ ( k9_relat_1 @ X17 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('50',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X42 ) @ X43 )
      | ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('53',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X25 @ X26 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('56',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k8_relset_1 @ X39 @ X40 @ X38 @ X41 )
        = ( k10_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('59',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ( ( k1_relat_1 @ sk_C )
        = ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['47','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('66',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('67',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14
        = ( k7_relat_1 @ X14 @ X15 ) )
      | ~ ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('71',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('73',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('77',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','75','76'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('79',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','75','76'])).

thf('80',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['43','77','78','79'])).

thf('81',plain,(
    $false ),
    inference(simplify,[status(thm)],['80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Uugpchq4ie
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:27:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 335 iterations in 0.208s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.45/0.67  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.45/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.67  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.67  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.45/0.67  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.67  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.67  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.67  thf(t39_relset_1, conjecture,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.45/0.67       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.45/0.67           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.45/0.67         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.45/0.67           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.67        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.45/0.67          ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.45/0.67              ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.45/0.67            ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.45/0.67              ( k1_relset_1 @ B @ A @ C ) ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t39_relset_1])).
% 0.45/0.67  thf('0', plain,
% 0.45/0.67      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.45/0.67          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.45/0.67          != (k2_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.45/0.67        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.45/0.67            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.45/0.67            != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('1', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.67         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 0.45/0.67          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.45/0.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.67  thf('3', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.45/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.67  thf('4', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.67  thf('5', plain,
% 0.45/0.67      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.67         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.45/0.67          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.45/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.67  thf('6', plain, (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.45/0.67      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.67  thf('7', plain,
% 0.45/0.67      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.45/0.67          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A)) != (k2_relat_1 @ sk_C))
% 0.45/0.67        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.45/0.67            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B)) != (k1_relat_1 @ sk_C)))),
% 0.45/0.67      inference('demod', [status(thm)], ['0', '3', '6'])).
% 0.45/0.67  thf('8', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(redefinition_k7_relset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.45/0.67  thf('9', plain,
% 0.45/0.67      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.45/0.67          | ((k7_relset_1 @ X35 @ X36 @ X34 @ X37) = (k9_relat_1 @ X34 @ X37)))),
% 0.45/0.67      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.45/0.67  thf('10', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(cc2_relset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.67  thf('13', plain,
% 0.45/0.67      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.67         ((v4_relat_1 @ X21 @ X22)
% 0.45/0.67          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.45/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.67  thf('14', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.45/0.67      inference('sup-', [status(thm)], ['12', '13'])).
% 0.45/0.67  thf(t209_relat_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.67       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.45/0.67  thf('15', plain,
% 0.45/0.67      (![X14 : $i, X15 : $i]:
% 0.45/0.67         (((X14) = (k7_relat_1 @ X14 @ X15))
% 0.45/0.67          | ~ (v4_relat_1 @ X14 @ X15)
% 0.45/0.67          | ~ (v1_relat_1 @ X14))),
% 0.45/0.67      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.67  thf('17', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(cc1_relset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( v1_relat_1 @ C ) ))).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.67         ((v1_relat_1 @ X18)
% 0.45/0.67          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.45/0.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.67  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.67      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.67  thf('20', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['16', '19'])).
% 0.45/0.67  thf(t148_relat_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( v1_relat_1 @ B ) =>
% 0.45/0.67       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.45/0.67  thf('21', plain,
% 0.45/0.67      (![X10 : $i, X11 : $i]:
% 0.45/0.67         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.45/0.67          | ~ (v1_relat_1 @ X10))),
% 0.45/0.67      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.45/0.67  thf('22', plain,
% 0.45/0.67      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))
% 0.45/0.67        | ~ (v1_relat_1 @ sk_C))),
% 0.45/0.67      inference('sup+', [status(thm)], ['20', '21'])).
% 0.45/0.67  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.67      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.67  thf('24', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['22', '23'])).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      ((((k9_relat_1 @ sk_C @ (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.45/0.67          != (k2_relat_1 @ sk_C))
% 0.45/0.67        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k2_relat_1 @ sk_C))
% 0.45/0.67            != (k1_relat_1 @ sk_C)))),
% 0.45/0.67      inference('demod', [status(thm)], ['7', '10', '11', '24'])).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(redefinition_k8_relset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.45/0.67  thf('27', plain,
% 0.45/0.67      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.45/0.67          | ((k8_relset_1 @ X39 @ X40 @ X38 @ X41) = (k10_relat_1 @ X38 @ X41)))),
% 0.45/0.67      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.45/0.67  thf('28', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['26', '27'])).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['26', '27'])).
% 0.45/0.67  thf('30', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('31', plain,
% 0.45/0.67      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.67         ((v5_relat_1 @ X21 @ X23)
% 0.45/0.67          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.45/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.67  thf('32', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.45/0.67      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.67  thf(d19_relat_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( v1_relat_1 @ B ) =>
% 0.45/0.67       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.67  thf('33', plain,
% 0.45/0.67      (![X8 : $i, X9 : $i]:
% 0.45/0.67         (~ (v5_relat_1 @ X8 @ X9)
% 0.45/0.67          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 0.45/0.67          | ~ (v1_relat_1 @ X8))),
% 0.45/0.67      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.45/0.67  thf('34', plain,
% 0.45/0.67      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.67  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.67      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.67  thf('36', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.45/0.67      inference('demod', [status(thm)], ['34', '35'])).
% 0.45/0.67  thf(t28_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.45/0.67  thf('37', plain,
% 0.45/0.67      (![X3 : $i, X4 : $i]:
% 0.45/0.67         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.45/0.67      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.45/0.67  thf('38', plain,
% 0.45/0.67      (((k3_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_A) = (k2_relat_1 @ sk_C))),
% 0.45/0.67      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.67  thf(t168_relat_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( v1_relat_1 @ B ) =>
% 0.45/0.67       ( ( k10_relat_1 @ B @ A ) =
% 0.45/0.67         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.45/0.67  thf('39', plain,
% 0.45/0.67      (![X12 : $i, X13 : $i]:
% 0.45/0.67         (((k10_relat_1 @ X12 @ X13)
% 0.45/0.67            = (k10_relat_1 @ X12 @ (k3_xboole_0 @ (k2_relat_1 @ X12) @ X13)))
% 0.45/0.67          | ~ (v1_relat_1 @ X12))),
% 0.45/0.67      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.45/0.67  thf('40', plain,
% 0.45/0.67      ((((k10_relat_1 @ sk_C @ sk_A)
% 0.45/0.67          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.45/0.67        | ~ (v1_relat_1 @ sk_C))),
% 0.45/0.67      inference('sup+', [status(thm)], ['38', '39'])).
% 0.45/0.67  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.67      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.67  thf('42', plain,
% 0.45/0.67      (((k10_relat_1 @ sk_C @ sk_A)
% 0.45/0.67         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.45/0.67      inference('demod', [status(thm)], ['40', '41'])).
% 0.45/0.67  thf('43', plain,
% 0.45/0.67      ((((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.45/0.67          != (k2_relat_1 @ sk_C))
% 0.45/0.67        | ((k10_relat_1 @ sk_C @ sk_A) != (k1_relat_1 @ sk_C)))),
% 0.45/0.67      inference('demod', [status(thm)], ['25', '28', '29', '42'])).
% 0.45/0.67  thf(d10_xboole_0, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.67  thf('44', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.45/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.67  thf('45', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.45/0.67      inference('simplify', [status(thm)], ['44'])).
% 0.45/0.67  thf(t146_funct_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( v1_relat_1 @ B ) =>
% 0.45/0.67       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.45/0.67         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.45/0.67  thf('46', plain,
% 0.45/0.67      (![X16 : $i, X17 : $i]:
% 0.45/0.67         (~ (r1_tarski @ X16 @ (k1_relat_1 @ X17))
% 0.45/0.67          | (r1_tarski @ X16 @ (k10_relat_1 @ X17 @ (k9_relat_1 @ X17 @ X16)))
% 0.45/0.67          | ~ (v1_relat_1 @ X17))),
% 0.45/0.67      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.45/0.67  thf('47', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ X0)
% 0.45/0.67          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.45/0.67             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.67  thf('48', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.45/0.67      inference('simplify', [status(thm)], ['44'])).
% 0.45/0.67  thf('49', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(t13_relset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.45/0.67       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.45/0.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.45/0.67  thf('50', plain,
% 0.45/0.67      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.45/0.67         (~ (r1_tarski @ (k1_relat_1 @ X42) @ X43)
% 0.45/0.67          | (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.45/0.67          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 0.45/0.67      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.45/0.67  thf('51', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))
% 0.45/0.67          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.67  thf('52', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['48', '51'])).
% 0.45/0.67  thf(dt_k8_relset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.45/0.67  thf('53', plain,
% 0.45/0.67      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.45/0.67          | (m1_subset_1 @ (k8_relset_1 @ X25 @ X26 @ X24 @ X27) @ 
% 0.45/0.67             (k1_zfmisc_1 @ X25)))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.45/0.67  thf('54', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (m1_subset_1 @ 
% 0.45/0.67          (k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C @ X0) @ 
% 0.45/0.67          (k1_zfmisc_1 @ (k1_relat_1 @ sk_C)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['52', '53'])).
% 0.45/0.67  thf('55', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['48', '51'])).
% 0.45/0.67  thf('56', plain,
% 0.45/0.67      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.45/0.67          | ((k8_relset_1 @ X39 @ X40 @ X38 @ X41) = (k10_relat_1 @ X38 @ X41)))),
% 0.45/0.67      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.45/0.67  thf('57', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((k8_relset_1 @ (k1_relat_1 @ sk_C) @ sk_A @ sk_C @ X0)
% 0.45/0.67           = (k10_relat_1 @ sk_C @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.67  thf('58', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (m1_subset_1 @ (k10_relat_1 @ sk_C @ X0) @ 
% 0.45/0.67          (k1_zfmisc_1 @ (k1_relat_1 @ sk_C)))),
% 0.45/0.67      inference('demod', [status(thm)], ['54', '57'])).
% 0.45/0.67  thf(t3_subset, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.67  thf('59', plain,
% 0.45/0.67      (![X5 : $i, X6 : $i]:
% 0.45/0.67         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.67  thf('60', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ (k1_relat_1 @ sk_C))),
% 0.45/0.67      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.67  thf('61', plain,
% 0.45/0.67      (![X0 : $i, X2 : $i]:
% 0.45/0.67         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.67  thf('62', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ X0))
% 0.45/0.67          | ((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ X0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['60', '61'])).
% 0.45/0.67  thf('63', plain,
% 0.45/0.67      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.67        | ((k1_relat_1 @ sk_C)
% 0.45/0.67            = (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['47', '62'])).
% 0.45/0.67  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.67      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.67  thf('65', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['48', '51'])).
% 0.45/0.67  thf('66', plain,
% 0.45/0.67      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.67         ((v4_relat_1 @ X21 @ X22)
% 0.45/0.67          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.45/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.67  thf('67', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.45/0.67      inference('sup-', [status(thm)], ['65', '66'])).
% 0.45/0.67  thf('68', plain,
% 0.45/0.67      (![X14 : $i, X15 : $i]:
% 0.45/0.67         (((X14) = (k7_relat_1 @ X14 @ X15))
% 0.45/0.67          | ~ (v4_relat_1 @ X14 @ X15)
% 0.45/0.67          | ~ (v1_relat_1 @ X14))),
% 0.45/0.67      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.45/0.67  thf('69', plain,
% 0.45/0.67      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.67        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['67', '68'])).
% 0.45/0.67  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.67      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.67  thf('71', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.45/0.67      inference('demod', [status(thm)], ['69', '70'])).
% 0.45/0.67  thf('72', plain,
% 0.45/0.67      (![X10 : $i, X11 : $i]:
% 0.45/0.67         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.45/0.67          | ~ (v1_relat_1 @ X10))),
% 0.45/0.67      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.45/0.67  thf('73', plain,
% 0.45/0.67      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.45/0.67        | ~ (v1_relat_1 @ sk_C))),
% 0.45/0.67      inference('sup+', [status(thm)], ['71', '72'])).
% 0.45/0.67  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.67      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.67  thf('75', plain,
% 0.45/0.67      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.45/0.67      inference('demod', [status(thm)], ['73', '74'])).
% 0.45/0.67  thf('76', plain,
% 0.45/0.67      (((k10_relat_1 @ sk_C @ sk_A)
% 0.45/0.67         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.45/0.67      inference('demod', [status(thm)], ['40', '41'])).
% 0.45/0.67  thf('77', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['63', '64', '75', '76'])).
% 0.45/0.67  thf('78', plain,
% 0.45/0.67      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.45/0.67      inference('demod', [status(thm)], ['73', '74'])).
% 0.45/0.67  thf('79', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['63', '64', '75', '76'])).
% 0.45/0.67  thf('80', plain,
% 0.45/0.67      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.45/0.67        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.45/0.67      inference('demod', [status(thm)], ['43', '77', '78', '79'])).
% 0.45/0.67  thf('81', plain, ($false), inference('simplify', [status(thm)], ['80'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.51/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

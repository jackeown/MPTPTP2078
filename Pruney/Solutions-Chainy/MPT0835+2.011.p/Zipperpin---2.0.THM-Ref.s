%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fLGuaL3Wut

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:45 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 448 expanded)
%              Number of leaves         :   36 ( 150 expanded)
%              Depth                    :   14
%              Number of atoms          :  895 (5733 expanded)
%              Number of equality atoms :   61 ( 307 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k7_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k9_relat_1 @ X32 @ X35 ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( X16
        = ( k7_relat_1 @ X16 @ X17 ) )
      | ~ ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k8_relset_1 @ X37 @ X38 @ X36 @ X39 )
        = ( k10_relat_1 @ X36 @ X39 ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( ( k10_relat_1 @ X14 @ X15 )
        = ( k10_relat_1 @ X14 @ ( k3_xboole_0 @ ( k2_relat_1 @ X14 ) @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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

thf('44',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X12 @ X13 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('51',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('55',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X40 ) @ X41 )
      | ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('59',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16
        = ( k7_relat_1 @ X16 @ X17 ) )
      | ~ ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('63',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('65',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('67',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('69',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( r1_tarski @ X18 @ ( k10_relat_1 @ X19 @ ( k9_relat_1 @ X19 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['67','70'])).

thf('72',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('74',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['51','74'])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('77',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['51','74'])).

thf('78',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['43','75','76','77'])).

thf('79',plain,(
    $false ),
    inference(simplify,[status(thm)],['78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fLGuaL3Wut
% 0.15/0.36  % Computer   : n020.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 15:25:22 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.22/0.36  % Number of cores: 8
% 0.22/0.36  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 306 iterations in 0.137s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.40/0.59  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.40/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.59  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.40/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.40/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.59  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.40/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.59  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.40/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.40/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.40/0.59  thf(t39_relset_1, conjecture,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.40/0.59       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.40/0.59           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.40/0.59         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.40/0.59           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.59        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.40/0.59          ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.40/0.59              ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.40/0.59            ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.40/0.59              ( k1_relset_1 @ B @ A @ C ) ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t39_relset_1])).
% 0.40/0.59  thf('0', plain,
% 0.40/0.59      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.40/0.59          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.40/0.59          != (k2_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.40/0.59        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.40/0.59            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.40/0.59            != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('1', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.40/0.59  thf('2', plain,
% 0.40/0.59      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.40/0.59         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.40/0.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.40/0.59  thf('3', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.59  thf('4', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.40/0.59  thf('5', plain,
% 0.40/0.59      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.40/0.59         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.40/0.59          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.40/0.59  thf('6', plain, (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.59  thf('7', plain,
% 0.40/0.59      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.40/0.59          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A)) != (k2_relat_1 @ sk_C))
% 0.40/0.59        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.40/0.59            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B)) != (k1_relat_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['0', '3', '6'])).
% 0.40/0.59  thf('8', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(redefinition_k7_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.40/0.59  thf('9', plain,
% 0.40/0.59      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.40/0.59          | ((k7_relset_1 @ X33 @ X34 @ X32 @ X35) = (k9_relat_1 @ X32 @ X35)))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.40/0.59  thf('10', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.40/0.59  thf('11', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.40/0.59  thf('12', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(cc2_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.40/0.59  thf('13', plain,
% 0.40/0.59      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.40/0.59         ((v4_relat_1 @ X23 @ X24)
% 0.40/0.59          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.59  thf('14', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.40/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.40/0.59  thf(t209_relat_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.40/0.59       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.40/0.59  thf('15', plain,
% 0.40/0.59      (![X16 : $i, X17 : $i]:
% 0.40/0.59         (((X16) = (k7_relat_1 @ X16 @ X17))
% 0.40/0.59          | ~ (v4_relat_1 @ X16 @ X17)
% 0.40/0.59          | ~ (v1_relat_1 @ X16))),
% 0.40/0.59      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.59  thf('17', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(cc1_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( v1_relat_1 @ C ) ))).
% 0.40/0.59  thf('18', plain,
% 0.40/0.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.40/0.59         ((v1_relat_1 @ X20)
% 0.40/0.59          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.40/0.59  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.40/0.59  thf('20', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['16', '19'])).
% 0.40/0.59  thf(t148_relat_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( v1_relat_1 @ B ) =>
% 0.40/0.59       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.40/0.59  thf('21', plain,
% 0.40/0.59      (![X10 : $i, X11 : $i]:
% 0.40/0.59         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.40/0.59          | ~ (v1_relat_1 @ X10))),
% 0.40/0.59      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.40/0.59  thf('22', plain,
% 0.40/0.59      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))
% 0.40/0.59        | ~ (v1_relat_1 @ sk_C))),
% 0.40/0.59      inference('sup+', [status(thm)], ['20', '21'])).
% 0.40/0.59  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.40/0.59  thf('24', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['22', '23'])).
% 0.40/0.59  thf('25', plain,
% 0.40/0.59      ((((k9_relat_1 @ sk_C @ (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.40/0.59          != (k2_relat_1 @ sk_C))
% 0.40/0.59        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k2_relat_1 @ sk_C))
% 0.40/0.59            != (k1_relat_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['7', '10', '11', '24'])).
% 0.40/0.59  thf('26', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(redefinition_k8_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.40/0.59  thf('27', plain,
% 0.40/0.59      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.40/0.59          | ((k8_relset_1 @ X37 @ X38 @ X36 @ X39) = (k10_relat_1 @ X36 @ X39)))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.40/0.59  thf('28', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.59  thf('29', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.59  thf('30', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('31', plain,
% 0.40/0.59      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.40/0.59         ((v5_relat_1 @ X23 @ X25)
% 0.40/0.59          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.59  thf('32', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.40/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.40/0.59  thf(d19_relat_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( v1_relat_1 @ B ) =>
% 0.40/0.59       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.40/0.59  thf('33', plain,
% 0.40/0.59      (![X8 : $i, X9 : $i]:
% 0.40/0.59         (~ (v5_relat_1 @ X8 @ X9)
% 0.40/0.59          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 0.40/0.59          | ~ (v1_relat_1 @ X8))),
% 0.40/0.59      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.40/0.59  thf('34', plain,
% 0.40/0.59      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.40/0.59  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.40/0.59  thf('36', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.40/0.59      inference('demod', [status(thm)], ['34', '35'])).
% 0.40/0.59  thf(t28_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.59  thf('37', plain,
% 0.40/0.59      (![X3 : $i, X4 : $i]:
% 0.40/0.59         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.59  thf('38', plain,
% 0.40/0.59      (((k3_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_A) = (k2_relat_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.40/0.59  thf(t168_relat_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( v1_relat_1 @ B ) =>
% 0.40/0.59       ( ( k10_relat_1 @ B @ A ) =
% 0.40/0.59         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.40/0.59  thf('39', plain,
% 0.40/0.59      (![X14 : $i, X15 : $i]:
% 0.40/0.59         (((k10_relat_1 @ X14 @ X15)
% 0.40/0.59            = (k10_relat_1 @ X14 @ (k3_xboole_0 @ (k2_relat_1 @ X14) @ X15)))
% 0.40/0.59          | ~ (v1_relat_1 @ X14))),
% 0.40/0.59      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.40/0.59  thf('40', plain,
% 0.40/0.59      ((((k10_relat_1 @ sk_C @ sk_A)
% 0.40/0.59          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.40/0.59        | ~ (v1_relat_1 @ sk_C))),
% 0.40/0.59      inference('sup+', [status(thm)], ['38', '39'])).
% 0.40/0.59  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.40/0.59  thf('42', plain,
% 0.40/0.59      (((k10_relat_1 @ sk_C @ sk_A)
% 0.40/0.59         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['40', '41'])).
% 0.40/0.59  thf('43', plain,
% 0.40/0.59      ((((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.40/0.59          != (k2_relat_1 @ sk_C))
% 0.40/0.59        | ((k10_relat_1 @ sk_C @ sk_A) != (k1_relat_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['25', '28', '29', '42'])).
% 0.40/0.59  thf('44', plain,
% 0.40/0.59      (((k10_relat_1 @ sk_C @ sk_A)
% 0.40/0.59         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['40', '41'])).
% 0.40/0.59  thf(t167_relat_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( v1_relat_1 @ B ) =>
% 0.40/0.59       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.40/0.59  thf('45', plain,
% 0.40/0.59      (![X12 : $i, X13 : $i]:
% 0.40/0.59         ((r1_tarski @ (k10_relat_1 @ X12 @ X13) @ (k1_relat_1 @ X12))
% 0.40/0.59          | ~ (v1_relat_1 @ X12))),
% 0.40/0.59      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.40/0.59  thf(d10_xboole_0, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.59  thf('46', plain,
% 0.40/0.59      (![X0 : $i, X2 : $i]:
% 0.40/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.40/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.59  thf('47', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.40/0.59          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.40/0.59  thf('48', plain,
% 0.40/0.59      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ sk_A))
% 0.40/0.59        | ((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.40/0.59        | ~ (v1_relat_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['44', '47'])).
% 0.40/0.59  thf('49', plain,
% 0.40/0.59      (((k10_relat_1 @ sk_C @ sk_A)
% 0.40/0.59         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['40', '41'])).
% 0.40/0.59  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.40/0.59  thf('51', plain,
% 0.40/0.59      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ sk_A))
% 0.40/0.59        | ((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_A)))),
% 0.40/0.59      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.40/0.59  thf('52', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.40/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.59  thf('53', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.40/0.59      inference('simplify', [status(thm)], ['52'])).
% 0.40/0.59  thf('54', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t13_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.40/0.59       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.40/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.40/0.59  thf('55', plain,
% 0.40/0.59      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.40/0.59         (~ (r1_tarski @ (k1_relat_1 @ X40) @ X41)
% 0.40/0.59          | (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.40/0.59          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 0.40/0.59      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.40/0.59  thf('56', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))
% 0.40/0.59          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['54', '55'])).
% 0.40/0.59  thf('57', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['53', '56'])).
% 0.40/0.59  thf('58', plain,
% 0.40/0.59      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.40/0.59         ((v4_relat_1 @ X23 @ X24)
% 0.40/0.59          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.59  thf('59', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['57', '58'])).
% 0.40/0.59  thf('60', plain,
% 0.40/0.59      (![X16 : $i, X17 : $i]:
% 0.40/0.59         (((X16) = (k7_relat_1 @ X16 @ X17))
% 0.40/0.59          | ~ (v4_relat_1 @ X16 @ X17)
% 0.40/0.59          | ~ (v1_relat_1 @ X16))),
% 0.40/0.59      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.40/0.59  thf('61', plain,
% 0.40/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.40/0.59        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['59', '60'])).
% 0.40/0.59  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.40/0.59  thf('63', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['61', '62'])).
% 0.40/0.59  thf('64', plain,
% 0.40/0.59      (![X10 : $i, X11 : $i]:
% 0.40/0.59         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.40/0.59          | ~ (v1_relat_1 @ X10))),
% 0.40/0.59      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.40/0.59  thf('65', plain,
% 0.40/0.59      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.40/0.59        | ~ (v1_relat_1 @ sk_C))),
% 0.40/0.59      inference('sup+', [status(thm)], ['63', '64'])).
% 0.40/0.59  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.40/0.59  thf('67', plain,
% 0.40/0.59      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['65', '66'])).
% 0.40/0.59  thf('68', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.40/0.59      inference('simplify', [status(thm)], ['52'])).
% 0.40/0.59  thf(t146_funct_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( v1_relat_1 @ B ) =>
% 0.40/0.59       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.40/0.59         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.40/0.59  thf('69', plain,
% 0.40/0.59      (![X18 : $i, X19 : $i]:
% 0.40/0.59         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 0.40/0.59          | (r1_tarski @ X18 @ (k10_relat_1 @ X19 @ (k9_relat_1 @ X19 @ X18)))
% 0.40/0.59          | ~ (v1_relat_1 @ X19))),
% 0.40/0.59      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.40/0.59  thf('70', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X0)
% 0.40/0.59          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.40/0.59             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['68', '69'])).
% 0.40/0.59  thf('71', plain,
% 0.40/0.59      (((r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 0.40/0.59         (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.40/0.59        | ~ (v1_relat_1 @ sk_C))),
% 0.40/0.59      inference('sup+', [status(thm)], ['67', '70'])).
% 0.40/0.59  thf('72', plain,
% 0.40/0.59      (((k10_relat_1 @ sk_C @ sk_A)
% 0.40/0.59         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['40', '41'])).
% 0.40/0.59  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.40/0.59  thf('74', plain,
% 0.40/0.59      ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.40/0.59  thf('75', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['51', '74'])).
% 0.40/0.59  thf('76', plain,
% 0.40/0.59      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['65', '66'])).
% 0.40/0.59  thf('77', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['51', '74'])).
% 0.40/0.59  thf('78', plain,
% 0.40/0.59      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.40/0.59        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['43', '75', '76', '77'])).
% 0.40/0.59  thf('79', plain, ($false), inference('simplify', [status(thm)], ['78'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.40/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

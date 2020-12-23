%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YFw0oet7JT

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:41 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 156 expanded)
%              Number of leaves         :   32 (  57 expanded)
%              Depth                    :   15
%              Number of atoms          :  808 (1870 expanded)
%              Number of equality atoms :   50 ( 123 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X17: $i] :
      ( ( ( k10_relat_1 @ X17 @ ( k2_relat_1 @ X17 ) )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X27 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X35 @ X33 )
        = ( k2_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( r1_tarski @ ( k10_relat_1 @ X20 @ X18 ) @ ( k10_relat_1 @ X20 @ X19 ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X15 @ X16 ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k8_relset_1 @ X41 @ X42 @ X40 @ X43 )
        = ( k10_relat_1 @ X40 @ X43 ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X24 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( r1_tarski @ ( k9_relat_1 @ X14 @ X12 ) @ ( k9_relat_1 @ X14 @ X13 ) ) ) ),
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

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X9 @ X10 ) @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('48',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['13','14'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('54',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k7_relset_1 @ X37 @ X38 @ X36 @ X39 )
        = ( k9_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('57',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('59',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('63',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['61','62'])).

thf('64',plain,(
    ( k10_relat_1 @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['32','63'])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YFw0oet7JT
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:03:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.66/0.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.66/0.85  % Solved by: fo/fo7.sh
% 0.66/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.85  % done 577 iterations in 0.381s
% 0.66/0.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.66/0.85  % SZS output start Refutation
% 0.66/0.85  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.66/0.85  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.66/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.85  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.66/0.85  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.66/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.66/0.85  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.66/0.85  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.66/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.85  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.66/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.66/0.85  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.66/0.85  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.66/0.85  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.66/0.85  thf(sk_C_type, type, sk_C: $i).
% 0.66/0.85  thf(t169_relat_1, axiom,
% 0.66/0.85    (![A:$i]:
% 0.66/0.85     ( ( v1_relat_1 @ A ) =>
% 0.66/0.85       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.66/0.85  thf('0', plain,
% 0.66/0.85      (![X17 : $i]:
% 0.66/0.85         (((k10_relat_1 @ X17 @ (k2_relat_1 @ X17)) = (k1_relat_1 @ X17))
% 0.66/0.85          | ~ (v1_relat_1 @ X17))),
% 0.66/0.85      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.66/0.85  thf(t38_relset_1, conjecture,
% 0.66/0.85    (![A:$i,B:$i,C:$i]:
% 0.66/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.85       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.66/0.85         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.66/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.85    (~( ![A:$i,B:$i,C:$i]:
% 0.66/0.85        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.85          ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.66/0.85            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) )),
% 0.66/0.85    inference('cnf.neg', [status(esa)], [t38_relset_1])).
% 0.66/0.85  thf('1', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(dt_k2_relset_1, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i]:
% 0.66/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.85       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.66/0.85  thf('2', plain,
% 0.66/0.85      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.66/0.85         ((m1_subset_1 @ (k2_relset_1 @ X27 @ X28 @ X29) @ (k1_zfmisc_1 @ X28))
% 0.66/0.85          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.66/0.85      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.66/0.85  thf('3', plain,
% 0.66/0.85      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.66/0.85      inference('sup-', [status(thm)], ['1', '2'])).
% 0.66/0.85  thf('4', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(redefinition_k2_relset_1, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i]:
% 0.66/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.85       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.66/0.85  thf('5', plain,
% 0.66/0.85      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.66/0.85         (((k2_relset_1 @ X34 @ X35 @ X33) = (k2_relat_1 @ X33))
% 0.66/0.85          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.66/0.85      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.66/0.85  thf('6', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.66/0.85      inference('sup-', [status(thm)], ['4', '5'])).
% 0.66/0.85  thf('7', plain, ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.66/0.85      inference('demod', [status(thm)], ['3', '6'])).
% 0.66/0.85  thf(t3_subset, axiom,
% 0.66/0.85    (![A:$i,B:$i]:
% 0.66/0.85     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.66/0.85  thf('8', plain,
% 0.66/0.85      (![X6 : $i, X7 : $i]:
% 0.66/0.85         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.66/0.85      inference('cnf', [status(esa)], [t3_subset])).
% 0.66/0.85  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.66/0.85      inference('sup-', [status(thm)], ['7', '8'])).
% 0.66/0.85  thf(t178_relat_1, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i]:
% 0.66/0.85     ( ( v1_relat_1 @ C ) =>
% 0.66/0.85       ( ( r1_tarski @ A @ B ) =>
% 0.66/0.85         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.66/0.85  thf('10', plain,
% 0.66/0.85      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.66/0.85         (~ (r1_tarski @ X18 @ X19)
% 0.66/0.85          | ~ (v1_relat_1 @ X20)
% 0.66/0.85          | (r1_tarski @ (k10_relat_1 @ X20 @ X18) @ (k10_relat_1 @ X20 @ X19)))),
% 0.66/0.85      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.66/0.85  thf('11', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((r1_tarski @ (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_C)) @ 
% 0.66/0.85           (k10_relat_1 @ X0 @ sk_B))
% 0.66/0.85          | ~ (v1_relat_1 @ X0))),
% 0.66/0.85      inference('sup-', [status(thm)], ['9', '10'])).
% 0.66/0.85  thf('12', plain,
% 0.66/0.85      (((r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ sk_B))
% 0.66/0.85        | ~ (v1_relat_1 @ sk_C)
% 0.66/0.85        | ~ (v1_relat_1 @ sk_C))),
% 0.66/0.85      inference('sup+', [status(thm)], ['0', '11'])).
% 0.66/0.85  thf('13', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(cc1_relset_1, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i]:
% 0.66/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.85       ( v1_relat_1 @ C ) ))).
% 0.66/0.85  thf('14', plain,
% 0.66/0.85      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.66/0.85         ((v1_relat_1 @ X21)
% 0.66/0.85          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.66/0.85      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.66/0.85  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.66/0.85      inference('sup-', [status(thm)], ['13', '14'])).
% 0.66/0.85  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 0.66/0.85      inference('sup-', [status(thm)], ['13', '14'])).
% 0.66/0.85  thf('17', plain,
% 0.66/0.85      ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.66/0.85      inference('demod', [status(thm)], ['12', '15', '16'])).
% 0.66/0.85  thf(t167_relat_1, axiom,
% 0.66/0.85    (![A:$i,B:$i]:
% 0.66/0.85     ( ( v1_relat_1 @ B ) =>
% 0.66/0.85       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.66/0.85  thf('18', plain,
% 0.66/0.85      (![X15 : $i, X16 : $i]:
% 0.66/0.85         ((r1_tarski @ (k10_relat_1 @ X15 @ X16) @ (k1_relat_1 @ X15))
% 0.66/0.85          | ~ (v1_relat_1 @ X15))),
% 0.66/0.85      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.66/0.85  thf(d10_xboole_0, axiom,
% 0.66/0.85    (![A:$i,B:$i]:
% 0.66/0.85     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.66/0.85  thf('19', plain,
% 0.66/0.85      (![X0 : $i, X2 : $i]:
% 0.66/0.85         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.66/0.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.66/0.85  thf('20', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ X0)
% 0.66/0.85          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.66/0.85          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['18', '19'])).
% 0.66/0.85  thf('21', plain,
% 0.66/0.85      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))
% 0.66/0.85        | ~ (v1_relat_1 @ sk_C))),
% 0.66/0.85      inference('sup-', [status(thm)], ['17', '20'])).
% 0.66/0.85  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.66/0.85      inference('sup-', [status(thm)], ['13', '14'])).
% 0.66/0.85  thf('23', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))),
% 0.66/0.85      inference('demod', [status(thm)], ['21', '22'])).
% 0.66/0.85  thf('24', plain,
% 0.66/0.85      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.66/0.85          != (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.66/0.85        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.66/0.85            != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('25', plain,
% 0.66/0.85      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.66/0.85          != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.66/0.85         <= (~
% 0.66/0.85             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.66/0.85                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.66/0.85      inference('split', [status(esa)], ['24'])).
% 0.66/0.85  thf('26', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(redefinition_k8_relset_1, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.85       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.66/0.85  thf('27', plain,
% 0.66/0.85      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.66/0.85         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.66/0.85          | ((k8_relset_1 @ X41 @ X42 @ X40 @ X43) = (k10_relat_1 @ X40 @ X43)))),
% 0.66/0.85      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.66/0.85  thf('28', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.66/0.85      inference('sup-', [status(thm)], ['26', '27'])).
% 0.66/0.85  thf('29', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(redefinition_k1_relset_1, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i]:
% 0.66/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.85       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.66/0.85  thf('30', plain,
% 0.66/0.85      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.66/0.85         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 0.66/0.85          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.66/0.85      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.66/0.85  thf('31', plain,
% 0.66/0.85      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.66/0.85      inference('sup-', [status(thm)], ['29', '30'])).
% 0.66/0.85  thf('32', plain,
% 0.66/0.85      ((((k10_relat_1 @ sk_C @ sk_B) != (k1_relat_1 @ sk_C)))
% 0.66/0.85         <= (~
% 0.66/0.85             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.66/0.85                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.66/0.85      inference('demod', [status(thm)], ['25', '28', '31'])).
% 0.66/0.85  thf(t146_relat_1, axiom,
% 0.66/0.85    (![A:$i]:
% 0.66/0.85     ( ( v1_relat_1 @ A ) =>
% 0.66/0.85       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.66/0.85  thf('33', plain,
% 0.66/0.85      (![X11 : $i]:
% 0.66/0.85         (((k9_relat_1 @ X11 @ (k1_relat_1 @ X11)) = (k2_relat_1 @ X11))
% 0.66/0.85          | ~ (v1_relat_1 @ X11))),
% 0.66/0.85      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.66/0.85  thf('34', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(dt_k1_relset_1, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i]:
% 0.66/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.85       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.66/0.85  thf('35', plain,
% 0.66/0.85      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.66/0.85         ((m1_subset_1 @ (k1_relset_1 @ X24 @ X25 @ X26) @ (k1_zfmisc_1 @ X24))
% 0.66/0.85          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.66/0.85      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.66/0.85  thf('36', plain,
% 0.66/0.85      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.66/0.85      inference('sup-', [status(thm)], ['34', '35'])).
% 0.66/0.85  thf('37', plain,
% 0.66/0.85      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.66/0.85      inference('sup-', [status(thm)], ['29', '30'])).
% 0.66/0.85  thf('38', plain,
% 0.66/0.85      ((m1_subset_1 @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.66/0.85      inference('demod', [status(thm)], ['36', '37'])).
% 0.66/0.85  thf('39', plain,
% 0.66/0.85      (![X6 : $i, X7 : $i]:
% 0.66/0.85         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.66/0.85      inference('cnf', [status(esa)], [t3_subset])).
% 0.66/0.85  thf('40', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.66/0.85      inference('sup-', [status(thm)], ['38', '39'])).
% 0.66/0.85  thf(t156_relat_1, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i]:
% 0.66/0.85     ( ( v1_relat_1 @ C ) =>
% 0.66/0.85       ( ( r1_tarski @ A @ B ) =>
% 0.66/0.85         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.66/0.85  thf('41', plain,
% 0.66/0.85      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.66/0.85         (~ (r1_tarski @ X12 @ X13)
% 0.66/0.85          | ~ (v1_relat_1 @ X14)
% 0.66/0.85          | (r1_tarski @ (k9_relat_1 @ X14 @ X12) @ (k9_relat_1 @ X14 @ X13)))),
% 0.66/0.85      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.66/0.85  thf('42', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_C)) @ 
% 0.66/0.85           (k9_relat_1 @ X0 @ sk_A))
% 0.66/0.85          | ~ (v1_relat_1 @ X0))),
% 0.66/0.85      inference('sup-', [status(thm)], ['40', '41'])).
% 0.66/0.85  thf('43', plain,
% 0.66/0.85      (((r1_tarski @ (k2_relat_1 @ sk_C) @ (k9_relat_1 @ sk_C @ sk_A))
% 0.66/0.85        | ~ (v1_relat_1 @ sk_C)
% 0.66/0.85        | ~ (v1_relat_1 @ sk_C))),
% 0.66/0.85      inference('sup+', [status(thm)], ['33', '42'])).
% 0.66/0.85  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.66/0.85      inference('sup-', [status(thm)], ['13', '14'])).
% 0.66/0.85  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.66/0.85      inference('sup-', [status(thm)], ['13', '14'])).
% 0.66/0.85  thf('46', plain,
% 0.66/0.85      ((r1_tarski @ (k2_relat_1 @ sk_C) @ (k9_relat_1 @ sk_C @ sk_A))),
% 0.66/0.85      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.66/0.85  thf(t144_relat_1, axiom,
% 0.66/0.85    (![A:$i,B:$i]:
% 0.66/0.85     ( ( v1_relat_1 @ B ) =>
% 0.66/0.85       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.66/0.85  thf('47', plain,
% 0.66/0.85      (![X9 : $i, X10 : $i]:
% 0.66/0.85         ((r1_tarski @ (k9_relat_1 @ X9 @ X10) @ (k2_relat_1 @ X9))
% 0.66/0.85          | ~ (v1_relat_1 @ X9))),
% 0.66/0.85      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.66/0.85  thf('48', plain,
% 0.66/0.85      (![X0 : $i, X2 : $i]:
% 0.66/0.85         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.66/0.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.66/0.85  thf('49', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i]:
% 0.66/0.85         (~ (v1_relat_1 @ X0)
% 0.66/0.85          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k9_relat_1 @ X0 @ X1))
% 0.66/0.85          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['47', '48'])).
% 0.66/0.85  thf('50', plain,
% 0.66/0.85      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.66/0.85        | ~ (v1_relat_1 @ sk_C))),
% 0.66/0.85      inference('sup-', [status(thm)], ['46', '49'])).
% 0.66/0.85  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.66/0.85      inference('sup-', [status(thm)], ['13', '14'])).
% 0.66/0.85  thf('52', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.66/0.85      inference('demod', [status(thm)], ['50', '51'])).
% 0.66/0.85  thf('53', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(redefinition_k7_relset_1, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.85       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.66/0.85  thf('54', plain,
% 0.66/0.85      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.66/0.85         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.66/0.85          | ((k7_relset_1 @ X37 @ X38 @ X36 @ X39) = (k9_relat_1 @ X36 @ X39)))),
% 0.66/0.85      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.66/0.85  thf('55', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.66/0.85      inference('sup-', [status(thm)], ['53', '54'])).
% 0.66/0.85  thf('56', plain,
% 0.66/0.85      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.66/0.85          != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.66/0.85         <= (~
% 0.66/0.85             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.66/0.85                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.66/0.85      inference('split', [status(esa)], ['24'])).
% 0.66/0.85  thf('57', plain,
% 0.66/0.85      ((((k9_relat_1 @ sk_C @ sk_A) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.66/0.85         <= (~
% 0.66/0.85             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.66/0.85                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.66/0.85      inference('sup-', [status(thm)], ['55', '56'])).
% 0.66/0.85  thf('58', plain,
% 0.66/0.85      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.66/0.85      inference('sup-', [status(thm)], ['4', '5'])).
% 0.66/0.85  thf('59', plain,
% 0.66/0.85      ((((k9_relat_1 @ sk_C @ sk_A) != (k2_relat_1 @ sk_C)))
% 0.66/0.85         <= (~
% 0.66/0.85             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.66/0.85                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.66/0.85      inference('demod', [status(thm)], ['57', '58'])).
% 0.66/0.85  thf('60', plain,
% 0.66/0.85      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.66/0.85         <= (~
% 0.66/0.85             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.66/0.85                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.66/0.85      inference('sup-', [status(thm)], ['52', '59'])).
% 0.66/0.85  thf('61', plain,
% 0.66/0.85      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.66/0.85          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.66/0.85      inference('simplify', [status(thm)], ['60'])).
% 0.66/0.85  thf('62', plain,
% 0.66/0.85      (~
% 0.66/0.85       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.66/0.85          = (k1_relset_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.66/0.85       ~
% 0.66/0.85       (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.66/0.85          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.66/0.85      inference('split', [status(esa)], ['24'])).
% 0.66/0.85  thf('63', plain,
% 0.66/0.85      (~
% 0.66/0.85       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.66/0.85          = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.66/0.85      inference('sat_resolution*', [status(thm)], ['61', '62'])).
% 0.66/0.85  thf('64', plain, (((k10_relat_1 @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.66/0.85      inference('simpl_trail', [status(thm)], ['32', '63'])).
% 0.66/0.85  thf('65', plain, ($false),
% 0.66/0.85      inference('simplify_reflect-', [status(thm)], ['23', '64'])).
% 0.66/0.85  
% 0.66/0.85  % SZS output end Refutation
% 0.66/0.85  
% 0.66/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

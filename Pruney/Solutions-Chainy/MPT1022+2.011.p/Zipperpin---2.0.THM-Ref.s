%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ifd6G64nkD

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:26 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 633 expanded)
%              Number of leaves         :   42 ( 209 expanded)
%              Depth                    :   16
%              Number of atoms          : 1532 (13044 expanded)
%              Number of equality atoms :   76 ( 577 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t92_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ A )
        & ( v3_funct_2 @ C @ A @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( r1_tarski @ B @ A )
       => ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) )
            = B )
          & ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) )
            = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ A )
          & ( v3_funct_2 @ C @ A @ A )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( r1_tarski @ B @ A )
         => ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) )
              = B )
            & ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) )
              = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t92_funct_2])).

thf('0',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('10',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['5','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12
        = ( k7_relat_1 @ X12 @ X13 ) )
      | ~ ( v4_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) )
        & ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( m1_subset_1 @ ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X38: $i,X39: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X38 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) )
      | ~ ( v3_funct_2 @ X39 @ X38 @ X38 )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X38 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('31',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k2_funct_2 @ X41 @ X40 )
        = ( k2_funct_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) )
      | ~ ( v3_funct_2 @ X40 @ X41 @ X41 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X41 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_funct_2 @ sk_A @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','36'])).

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('42',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k9_relat_1 @ X18 @ X19 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X18 ) @ X19 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('43',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X14 @ ( k10_relat_1 @ X14 @ X15 ) ) @ X15 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) )
      | ~ ( v3_funct_2 @ X39 @ X38 @ X38 )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X38 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('48',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,
    ( ( k2_funct_2 @ sk_A @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('54',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('56',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v3_funct_2 @ X33 @ X34 @ X35 )
      | ( v2_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('57',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['45','54','60','61','62'])).

thf('64',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['23','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v3_funct_2 @ X33 @ X34 @ X35 )
      | ( v2_funct_2 @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('67',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['67','68','69'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('71',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v2_funct_2 @ X37 @ X36 )
      | ( ( k2_relat_1 @ X37 )
        = X36 )
      | ~ ( v5_relat_1 @ X37 @ X36 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('76',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['72','73','76'])).

thf('78',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','36'])).

thf('79',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('80',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12
        = ( k7_relat_1 @ X12 @ X13 ) )
      | ~ ( v4_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('84',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('86',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','36'])).

thf('88',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v3_funct_2 @ X33 @ X34 @ X35 )
      | ( v2_funct_2 @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('89',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X38 @ X39 ) @ X38 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) )
      | ~ ( v3_funct_2 @ X39 @ X38 @ X38 )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X38 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('92',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k2_funct_2 @ sk_A @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('97',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['92','93','94','95','96'])).

thf('98',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('99',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['89','97','98'])).

thf('100',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v2_funct_2 @ X37 @ X36 )
      | ( ( k2_relat_1 @ X37 )
        = X36 )
      | ~ ( v5_relat_1 @ X37 @ X36 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('101',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('103',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','36'])).

thf('104',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('105',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['101','102','105'])).

thf('107',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('108',plain,
    ( sk_A
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['86','106','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('110',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','77','108','109'])).

thf('111',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['13','110'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('112',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v2_funct_1 @ X21 )
      | ( ( k10_relat_1 @ X21 @ ( k9_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('115',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['113','114','115','116'])).

thf('118',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('120',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k8_relset_1 @ X30 @ X31 @ X29 @ X32 )
        = ( k10_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('123',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k7_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k9_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['125'])).

thf('127',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['124','126'])).

thf('128',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['121','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('130',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['125'])).

thf('131',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('133',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['72','73','76'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('135',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k2_relat_1 @ X17 ) )
      | ( ( k9_relat_1 @ X17 @ ( k10_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['133','139'])).

thf('141',plain,
    ( ( sk_B != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['131','132','140'])).

thf('142',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
    = sk_B ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['125'])).

thf('144',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['142','143'])).

thf('145',plain,(
    ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['128','144'])).

thf('146',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['118','145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ifd6G64nkD
% 0.15/0.37  % Computer   : n020.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 11:08:52 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 0.50/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.74  % Solved by: fo/fo7.sh
% 0.50/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.74  % done 325 iterations in 0.252s
% 0.50/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.74  % SZS output start Refutation
% 0.50/0.74  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.50/0.74  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.50/0.74  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.50/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.50/0.74  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.50/0.74  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.50/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.50/0.74  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.50/0.74  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.50/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.50/0.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.50/0.74  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.50/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.74  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.50/0.74  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.50/0.74  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.50/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.74  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.50/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.50/0.74  thf(t92_funct_2, conjecture,
% 0.50/0.74    (![A:$i,B:$i,C:$i]:
% 0.50/0.74     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.50/0.74         ( v3_funct_2 @ C @ A @ A ) & 
% 0.50/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.50/0.74       ( ( r1_tarski @ B @ A ) =>
% 0.50/0.74         ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.50/0.74             ( B ) ) & 
% 0.50/0.74           ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.50/0.74             ( B ) ) ) ) ))).
% 0.50/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.74    (~( ![A:$i,B:$i,C:$i]:
% 0.50/0.74        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.50/0.74            ( v3_funct_2 @ C @ A @ A ) & 
% 0.50/0.74            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.50/0.74          ( ( r1_tarski @ B @ A ) =>
% 0.50/0.74            ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.50/0.74                ( B ) ) & 
% 0.50/0.74              ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.50/0.74                ( B ) ) ) ) ) )),
% 0.50/0.74    inference('cnf.neg', [status(esa)], [t92_funct_2])).
% 0.50/0.74  thf('0', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('1', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf(cc2_relset_1, axiom,
% 0.50/0.74    (![A:$i,B:$i,C:$i]:
% 0.50/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.74       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.50/0.74  thf('2', plain,
% 0.50/0.74      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.50/0.74         ((v4_relat_1 @ X22 @ X23)
% 0.50/0.74          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.50/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.50/0.74  thf('3', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.50/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.74  thf(d18_relat_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( v1_relat_1 @ B ) =>
% 0.50/0.74       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.50/0.74  thf('4', plain,
% 0.50/0.74      (![X5 : $i, X6 : $i]:
% 0.50/0.74         (~ (v4_relat_1 @ X5 @ X6)
% 0.50/0.74          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.50/0.74          | ~ (v1_relat_1 @ X5))),
% 0.50/0.74      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.50/0.74  thf('5', plain,
% 0.50/0.74      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.50/0.74      inference('sup-', [status(thm)], ['3', '4'])).
% 0.50/0.74  thf('6', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf(cc2_relat_1, axiom,
% 0.50/0.74    (![A:$i]:
% 0.50/0.74     ( ( v1_relat_1 @ A ) =>
% 0.50/0.74       ( ![B:$i]:
% 0.50/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.50/0.74  thf('7', plain,
% 0.50/0.74      (![X3 : $i, X4 : $i]:
% 0.50/0.74         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.50/0.74          | (v1_relat_1 @ X3)
% 0.50/0.74          | ~ (v1_relat_1 @ X4))),
% 0.50/0.74      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.50/0.74  thf('8', plain,
% 0.50/0.74      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.50/0.74      inference('sup-', [status(thm)], ['6', '7'])).
% 0.50/0.74  thf(fc6_relat_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.50/0.74  thf('9', plain,
% 0.50/0.74      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.50/0.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.50/0.74  thf('10', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.74      inference('demod', [status(thm)], ['8', '9'])).
% 0.50/0.74  thf('11', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.50/0.74      inference('demod', [status(thm)], ['5', '10'])).
% 0.50/0.74  thf(d10_xboole_0, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.74  thf('12', plain,
% 0.50/0.74      (![X0 : $i, X2 : $i]:
% 0.50/0.74         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.50/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.74  thf('13', plain,
% 0.50/0.74      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))
% 0.50/0.74        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['11', '12'])).
% 0.50/0.74  thf('14', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.50/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.74  thf('15', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.50/0.74      inference('simplify', [status(thm)], ['14'])).
% 0.50/0.74  thf('16', plain,
% 0.50/0.74      (![X5 : $i, X6 : $i]:
% 0.50/0.74         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.50/0.74          | (v4_relat_1 @ X5 @ X6)
% 0.50/0.74          | ~ (v1_relat_1 @ X5))),
% 0.50/0.74      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.50/0.74  thf('17', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['15', '16'])).
% 0.50/0.74  thf(t209_relat_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.50/0.74       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.50/0.74  thf('18', plain,
% 0.50/0.74      (![X12 : $i, X13 : $i]:
% 0.50/0.74         (((X12) = (k7_relat_1 @ X12 @ X13))
% 0.50/0.74          | ~ (v4_relat_1 @ X12 @ X13)
% 0.50/0.74          | ~ (v1_relat_1 @ X12))),
% 0.50/0.74      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.50/0.74  thf('19', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (~ (v1_relat_1 @ X0)
% 0.50/0.74          | ~ (v1_relat_1 @ X0)
% 0.50/0.74          | ((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.50/0.74      inference('sup-', [status(thm)], ['17', '18'])).
% 0.50/0.74  thf('20', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 0.50/0.74      inference('simplify', [status(thm)], ['19'])).
% 0.50/0.74  thf(t148_relat_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( v1_relat_1 @ B ) =>
% 0.50/0.74       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.50/0.74  thf('21', plain,
% 0.50/0.74      (![X9 : $i, X10 : $i]:
% 0.50/0.74         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.50/0.74          | ~ (v1_relat_1 @ X9))),
% 0.50/0.74      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.50/0.74  thf('22', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.50/0.74          | ~ (v1_relat_1 @ X0)
% 0.50/0.74          | ~ (v1_relat_1 @ X0))),
% 0.50/0.74      inference('sup+', [status(thm)], ['20', '21'])).
% 0.50/0.74  thf('23', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (~ (v1_relat_1 @ X0)
% 0.50/0.74          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.50/0.74      inference('simplify', [status(thm)], ['22'])).
% 0.50/0.74  thf('24', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf(dt_k2_funct_2, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.50/0.74         ( v3_funct_2 @ B @ A @ A ) & 
% 0.50/0.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.50/0.74       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.50/0.74         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.50/0.74         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.50/0.74         ( m1_subset_1 @
% 0.50/0.74           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.50/0.74  thf('25', plain,
% 0.50/0.74      (![X38 : $i, X39 : $i]:
% 0.50/0.74         ((m1_subset_1 @ (k2_funct_2 @ X38 @ X39) @ 
% 0.50/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))
% 0.50/0.74          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))
% 0.50/0.74          | ~ (v3_funct_2 @ X39 @ X38 @ X38)
% 0.50/0.74          | ~ (v1_funct_2 @ X39 @ X38 @ X38)
% 0.50/0.74          | ~ (v1_funct_1 @ X39))),
% 0.50/0.74      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.50/0.74  thf('26', plain,
% 0.50/0.74      ((~ (v1_funct_1 @ sk_C)
% 0.50/0.74        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.50/0.74        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.50/0.74        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_C) @ 
% 0.50/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.50/0.74      inference('sup-', [status(thm)], ['24', '25'])).
% 0.50/0.74  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('28', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('29', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('30', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf(redefinition_k2_funct_2, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.50/0.74         ( v3_funct_2 @ B @ A @ A ) & 
% 0.50/0.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.50/0.74       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.50/0.74  thf('31', plain,
% 0.50/0.74      (![X40 : $i, X41 : $i]:
% 0.50/0.74         (((k2_funct_2 @ X41 @ X40) = (k2_funct_1 @ X40))
% 0.50/0.74          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))
% 0.50/0.74          | ~ (v3_funct_2 @ X40 @ X41 @ X41)
% 0.50/0.74          | ~ (v1_funct_2 @ X40 @ X41 @ X41)
% 0.50/0.74          | ~ (v1_funct_1 @ X40))),
% 0.50/0.74      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.50/0.74  thf('32', plain,
% 0.50/0.74      ((~ (v1_funct_1 @ sk_C)
% 0.50/0.74        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.50/0.74        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.50/0.74        | ((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['30', '31'])).
% 0.50/0.74  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('35', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('36', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.50/0.74      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.50/0.74  thf('37', plain,
% 0.50/0.74      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.50/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.50/0.74      inference('demod', [status(thm)], ['26', '27', '28', '29', '36'])).
% 0.50/0.74  thf('38', plain,
% 0.50/0.74      (![X3 : $i, X4 : $i]:
% 0.50/0.74         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.50/0.74          | (v1_relat_1 @ X3)
% 0.50/0.74          | ~ (v1_relat_1 @ X4))),
% 0.50/0.74      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.50/0.74  thf('39', plain,
% 0.50/0.74      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 0.50/0.74        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['37', '38'])).
% 0.50/0.74  thf('40', plain,
% 0.50/0.74      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.50/0.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.50/0.74  thf('41', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.50/0.74      inference('demod', [status(thm)], ['39', '40'])).
% 0.50/0.74  thf(t154_funct_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.50/0.74       ( ( v2_funct_1 @ B ) =>
% 0.50/0.74         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.50/0.74  thf('42', plain,
% 0.50/0.74      (![X18 : $i, X19 : $i]:
% 0.50/0.74         (~ (v2_funct_1 @ X18)
% 0.50/0.74          | ((k9_relat_1 @ X18 @ X19)
% 0.50/0.74              = (k10_relat_1 @ (k2_funct_1 @ X18) @ X19))
% 0.50/0.74          | ~ (v1_funct_1 @ X18)
% 0.50/0.74          | ~ (v1_relat_1 @ X18))),
% 0.50/0.74      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.50/0.74  thf(t145_funct_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.50/0.74       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.50/0.74  thf('43', plain,
% 0.50/0.74      (![X14 : $i, X15 : $i]:
% 0.50/0.74         ((r1_tarski @ (k9_relat_1 @ X14 @ (k10_relat_1 @ X14 @ X15)) @ X15)
% 0.50/0.74          | ~ (v1_funct_1 @ X14)
% 0.50/0.74          | ~ (v1_relat_1 @ X14))),
% 0.50/0.74      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.50/0.74  thf('44', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         ((r1_tarski @ 
% 0.50/0.74           (k9_relat_1 @ (k2_funct_1 @ X1) @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 0.50/0.74          | ~ (v1_relat_1 @ X1)
% 0.50/0.74          | ~ (v1_funct_1 @ X1)
% 0.50/0.74          | ~ (v2_funct_1 @ X1)
% 0.50/0.74          | ~ (v1_relat_1 @ (k2_funct_1 @ X1))
% 0.50/0.74          | ~ (v1_funct_1 @ (k2_funct_1 @ X1)))),
% 0.50/0.74      inference('sup+', [status(thm)], ['42', '43'])).
% 0.50/0.74  thf('45', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.74          | ~ (v2_funct_1 @ sk_C)
% 0.50/0.74          | ~ (v1_funct_1 @ sk_C)
% 0.50/0.74          | ~ (v1_relat_1 @ sk_C)
% 0.50/0.74          | (r1_tarski @ 
% 0.50/0.74             (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k9_relat_1 @ sk_C @ X0)) @ X0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['41', '44'])).
% 0.50/0.74  thf('46', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('47', plain,
% 0.50/0.74      (![X38 : $i, X39 : $i]:
% 0.50/0.74         ((v1_funct_1 @ (k2_funct_2 @ X38 @ X39))
% 0.50/0.74          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))
% 0.50/0.74          | ~ (v3_funct_2 @ X39 @ X38 @ X38)
% 0.50/0.74          | ~ (v1_funct_2 @ X39 @ X38 @ X38)
% 0.50/0.74          | ~ (v1_funct_1 @ X39))),
% 0.50/0.74      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.50/0.74  thf('48', plain,
% 0.50/0.74      ((~ (v1_funct_1 @ sk_C)
% 0.50/0.74        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.50/0.74        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.50/0.74        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_C)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['46', '47'])).
% 0.50/0.74  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('50', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('51', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('52', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_C))),
% 0.50/0.74      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.50/0.74  thf('53', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.50/0.74      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.50/0.74  thf('54', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.50/0.74      inference('demod', [status(thm)], ['52', '53'])).
% 0.50/0.74  thf('55', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf(cc2_funct_2, axiom,
% 0.50/0.74    (![A:$i,B:$i,C:$i]:
% 0.50/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.74       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.50/0.74         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.50/0.74  thf('56', plain,
% 0.50/0.74      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.50/0.74         (~ (v1_funct_1 @ X33)
% 0.50/0.74          | ~ (v3_funct_2 @ X33 @ X34 @ X35)
% 0.50/0.74          | (v2_funct_1 @ X33)
% 0.50/0.74          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.50/0.74      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.50/0.74  thf('57', plain,
% 0.50/0.74      (((v2_funct_1 @ sk_C)
% 0.50/0.74        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.50/0.74        | ~ (v1_funct_1 @ sk_C))),
% 0.50/0.74      inference('sup-', [status(thm)], ['55', '56'])).
% 0.50/0.74  thf('58', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('60', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.74      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.50/0.74  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.74      inference('demod', [status(thm)], ['8', '9'])).
% 0.50/0.74  thf('63', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (r1_tarski @ 
% 0.50/0.74          (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k9_relat_1 @ sk_C @ X0)) @ X0)),
% 0.50/0.74      inference('demod', [status(thm)], ['45', '54', '60', '61', '62'])).
% 0.50/0.74  thf('64', plain,
% 0.50/0.74      (((r1_tarski @ 
% 0.50/0.74         (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)) @ 
% 0.50/0.74         (k1_relat_1 @ sk_C))
% 0.50/0.74        | ~ (v1_relat_1 @ sk_C))),
% 0.50/0.74      inference('sup+', [status(thm)], ['23', '63'])).
% 0.50/0.74  thf('65', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('66', plain,
% 0.50/0.74      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.50/0.74         (~ (v1_funct_1 @ X33)
% 0.50/0.74          | ~ (v3_funct_2 @ X33 @ X34 @ X35)
% 0.50/0.74          | (v2_funct_2 @ X33 @ X35)
% 0.50/0.74          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.50/0.74      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.50/0.74  thf('67', plain,
% 0.50/0.74      (((v2_funct_2 @ sk_C @ sk_A)
% 0.50/0.74        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.50/0.74        | ~ (v1_funct_1 @ sk_C))),
% 0.50/0.74      inference('sup-', [status(thm)], ['65', '66'])).
% 0.50/0.74  thf('68', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('70', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.50/0.74      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.50/0.74  thf(d3_funct_2, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.50/0.74       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.50/0.74  thf('71', plain,
% 0.50/0.74      (![X36 : $i, X37 : $i]:
% 0.50/0.74         (~ (v2_funct_2 @ X37 @ X36)
% 0.50/0.74          | ((k2_relat_1 @ X37) = (X36))
% 0.50/0.74          | ~ (v5_relat_1 @ X37 @ X36)
% 0.50/0.74          | ~ (v1_relat_1 @ X37))),
% 0.50/0.74      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.50/0.74  thf('72', plain,
% 0.50/0.74      ((~ (v1_relat_1 @ sk_C)
% 0.50/0.74        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.50/0.74        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['70', '71'])).
% 0.50/0.74  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.74      inference('demod', [status(thm)], ['8', '9'])).
% 0.50/0.74  thf('74', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('75', plain,
% 0.50/0.74      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.50/0.74         ((v5_relat_1 @ X22 @ X24)
% 0.50/0.74          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.50/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.50/0.74  thf('76', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.50/0.74      inference('sup-', [status(thm)], ['74', '75'])).
% 0.50/0.74  thf('77', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.50/0.74      inference('demod', [status(thm)], ['72', '73', '76'])).
% 0.50/0.74  thf('78', plain,
% 0.50/0.74      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.50/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.50/0.74      inference('demod', [status(thm)], ['26', '27', '28', '29', '36'])).
% 0.50/0.74  thf('79', plain,
% 0.50/0.74      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.50/0.74         ((v4_relat_1 @ X22 @ X23)
% 0.50/0.74          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.50/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.50/0.74  thf('80', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.50/0.74      inference('sup-', [status(thm)], ['78', '79'])).
% 0.50/0.74  thf('81', plain,
% 0.50/0.74      (![X12 : $i, X13 : $i]:
% 0.50/0.74         (((X12) = (k7_relat_1 @ X12 @ X13))
% 0.50/0.74          | ~ (v4_relat_1 @ X12 @ X13)
% 0.50/0.74          | ~ (v1_relat_1 @ X12))),
% 0.50/0.74      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.50/0.74  thf('82', plain,
% 0.50/0.74      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.74        | ((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['80', '81'])).
% 0.50/0.74  thf('83', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.50/0.74      inference('demod', [status(thm)], ['39', '40'])).
% 0.50/0.74  thf('84', plain,
% 0.50/0.74      (((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))),
% 0.50/0.74      inference('demod', [status(thm)], ['82', '83'])).
% 0.50/0.74  thf('85', plain,
% 0.50/0.74      (![X9 : $i, X10 : $i]:
% 0.50/0.74         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.50/0.74          | ~ (v1_relat_1 @ X9))),
% 0.50/0.74      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.50/0.74  thf('86', plain,
% 0.50/0.74      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.74          = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))
% 0.50/0.74        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.50/0.74      inference('sup+', [status(thm)], ['84', '85'])).
% 0.50/0.74  thf('87', plain,
% 0.50/0.74      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.50/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.50/0.74      inference('demod', [status(thm)], ['26', '27', '28', '29', '36'])).
% 0.50/0.74  thf('88', plain,
% 0.50/0.74      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.50/0.74         (~ (v1_funct_1 @ X33)
% 0.50/0.74          | ~ (v3_funct_2 @ X33 @ X34 @ X35)
% 0.50/0.74          | (v2_funct_2 @ X33 @ X35)
% 0.50/0.74          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.50/0.74      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.50/0.74  thf('89', plain,
% 0.50/0.74      (((v2_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A)
% 0.50/0.74        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)
% 0.50/0.74        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['87', '88'])).
% 0.50/0.74  thf('90', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('91', plain,
% 0.50/0.74      (![X38 : $i, X39 : $i]:
% 0.50/0.74         ((v3_funct_2 @ (k2_funct_2 @ X38 @ X39) @ X38 @ X38)
% 0.50/0.74          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))
% 0.50/0.74          | ~ (v3_funct_2 @ X39 @ X38 @ X38)
% 0.50/0.74          | ~ (v1_funct_2 @ X39 @ X38 @ X38)
% 0.50/0.74          | ~ (v1_funct_1 @ X39))),
% 0.50/0.74      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.50/0.74  thf('92', plain,
% 0.50/0.74      ((~ (v1_funct_1 @ sk_C)
% 0.50/0.74        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.50/0.74        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.50/0.74        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A @ sk_A))),
% 0.50/0.74      inference('sup-', [status(thm)], ['90', '91'])).
% 0.50/0.74  thf('93', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('94', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('95', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('96', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.50/0.74      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.50/0.74  thf('97', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)),
% 0.50/0.74      inference('demod', [status(thm)], ['92', '93', '94', '95', '96'])).
% 0.50/0.74  thf('98', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.50/0.74      inference('demod', [status(thm)], ['52', '53'])).
% 0.50/0.74  thf('99', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.50/0.74      inference('demod', [status(thm)], ['89', '97', '98'])).
% 0.50/0.74  thf('100', plain,
% 0.50/0.74      (![X36 : $i, X37 : $i]:
% 0.50/0.74         (~ (v2_funct_2 @ X37 @ X36)
% 0.50/0.74          | ((k2_relat_1 @ X37) = (X36))
% 0.50/0.74          | ~ (v5_relat_1 @ X37 @ X36)
% 0.50/0.74          | ~ (v1_relat_1 @ X37))),
% 0.50/0.74      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.50/0.74  thf('101', plain,
% 0.50/0.74      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.50/0.74        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)
% 0.50/0.74        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['99', '100'])).
% 0.50/0.74  thf('102', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.50/0.74      inference('demod', [status(thm)], ['39', '40'])).
% 0.50/0.74  thf('103', plain,
% 0.50/0.74      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.50/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.50/0.74      inference('demod', [status(thm)], ['26', '27', '28', '29', '36'])).
% 0.50/0.74  thf('104', plain,
% 0.50/0.74      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.50/0.74         ((v5_relat_1 @ X22 @ X24)
% 0.50/0.74          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.50/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.50/0.74  thf('105', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.50/0.74      inference('sup-', [status(thm)], ['103', '104'])).
% 0.50/0.74  thf('106', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 0.50/0.74      inference('demod', [status(thm)], ['101', '102', '105'])).
% 0.50/0.74  thf('107', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.50/0.74      inference('demod', [status(thm)], ['39', '40'])).
% 0.50/0.74  thf('108', plain, (((sk_A) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))),
% 0.50/0.74      inference('demod', [status(thm)], ['86', '106', '107'])).
% 0.50/0.74  thf('109', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.74      inference('demod', [status(thm)], ['8', '9'])).
% 0.50/0.74  thf('110', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.50/0.74      inference('demod', [status(thm)], ['64', '77', '108', '109'])).
% 0.50/0.74  thf('111', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.50/0.74      inference('demod', [status(thm)], ['13', '110'])).
% 0.50/0.74  thf(t164_funct_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.50/0.74       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.50/0.74         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.50/0.74  thf('112', plain,
% 0.50/0.74      (![X20 : $i, X21 : $i]:
% 0.50/0.74         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 0.50/0.74          | ~ (v2_funct_1 @ X21)
% 0.50/0.74          | ((k10_relat_1 @ X21 @ (k9_relat_1 @ X21 @ X20)) = (X20))
% 0.50/0.74          | ~ (v1_funct_1 @ X21)
% 0.50/0.74          | ~ (v1_relat_1 @ X21))),
% 0.50/0.74      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.50/0.74  thf('113', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (~ (r1_tarski @ X0 @ sk_A)
% 0.50/0.74          | ~ (v1_relat_1 @ sk_C)
% 0.50/0.74          | ~ (v1_funct_1 @ sk_C)
% 0.50/0.74          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0))
% 0.50/0.74          | ~ (v2_funct_1 @ sk_C))),
% 0.50/0.74      inference('sup-', [status(thm)], ['111', '112'])).
% 0.50/0.74  thf('114', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.74      inference('demod', [status(thm)], ['8', '9'])).
% 0.50/0.74  thf('115', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('116', plain, ((v2_funct_1 @ sk_C)),
% 0.50/0.74      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.50/0.74  thf('117', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (~ (r1_tarski @ X0 @ sk_A)
% 0.50/0.74          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.50/0.74      inference('demod', [status(thm)], ['113', '114', '115', '116'])).
% 0.50/0.74  thf('118', plain,
% 0.50/0.74      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.50/0.74      inference('sup-', [status(thm)], ['0', '117'])).
% 0.50/0.74  thf('119', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf(redefinition_k8_relset_1, axiom,
% 0.50/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.74       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.50/0.74  thf('120', plain,
% 0.50/0.74      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.50/0.74         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.50/0.74          | ((k8_relset_1 @ X30 @ X31 @ X29 @ X32) = (k10_relat_1 @ X29 @ X32)))),
% 0.50/0.74      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.50/0.74  thf('121', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['119', '120'])).
% 0.50/0.74  thf('122', plain,
% 0.50/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf(redefinition_k7_relset_1, axiom,
% 0.50/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.74       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.50/0.74  thf('123', plain,
% 0.50/0.74      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.50/0.74         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.50/0.74          | ((k7_relset_1 @ X26 @ X27 @ X25 @ X28) = (k9_relat_1 @ X25 @ X28)))),
% 0.50/0.74      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.50/0.74  thf('124', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['122', '123'])).
% 0.50/0.74  thf('125', plain,
% 0.50/0.74      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.50/0.74          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B))
% 0.50/0.74        | ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.50/0.74            (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('126', plain,
% 0.50/0.74      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.50/0.74          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.50/0.74         <= (~
% 0.50/0.74             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.50/0.74                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.50/0.74      inference('split', [status(esa)], ['125'])).
% 0.50/0.74  thf('127', plain,
% 0.50/0.74      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.50/0.74          != (sk_B)))
% 0.50/0.74         <= (~
% 0.50/0.74             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.50/0.74                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.50/0.74      inference('sup-', [status(thm)], ['124', '126'])).
% 0.50/0.74  thf('128', plain,
% 0.50/0.74      ((((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B)))
% 0.50/0.74         <= (~
% 0.50/0.74             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.50/0.74                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.50/0.74      inference('sup-', [status(thm)], ['121', '127'])).
% 0.50/0.74  thf('129', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['119', '120'])).
% 0.50/0.74  thf('130', plain,
% 0.50/0.74      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.50/0.74          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.50/0.74         <= (~
% 0.50/0.74             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.50/0.74                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.50/0.74      inference('split', [status(esa)], ['125'])).
% 0.50/0.74  thf('131', plain,
% 0.50/0.74      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ (k10_relat_1 @ sk_C @ sk_B))
% 0.50/0.74          != (sk_B)))
% 0.50/0.74         <= (~
% 0.50/0.74             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.50/0.74                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.50/0.74      inference('sup-', [status(thm)], ['129', '130'])).
% 0.50/0.74  thf('132', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['122', '123'])).
% 0.50/0.74  thf('133', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('134', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.50/0.74      inference('demod', [status(thm)], ['72', '73', '76'])).
% 0.50/0.74  thf(t147_funct_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.50/0.74       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.50/0.74         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.50/0.74  thf('135', plain,
% 0.50/0.74      (![X16 : $i, X17 : $i]:
% 0.50/0.74         (~ (r1_tarski @ X16 @ (k2_relat_1 @ X17))
% 0.50/0.74          | ((k9_relat_1 @ X17 @ (k10_relat_1 @ X17 @ X16)) = (X16))
% 0.50/0.74          | ~ (v1_funct_1 @ X17)
% 0.50/0.74          | ~ (v1_relat_1 @ X17))),
% 0.50/0.74      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.50/0.74  thf('136', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (~ (r1_tarski @ X0 @ sk_A)
% 0.50/0.74          | ~ (v1_relat_1 @ sk_C)
% 0.50/0.74          | ~ (v1_funct_1 @ sk_C)
% 0.50/0.74          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['134', '135'])).
% 0.50/0.74  thf('137', plain, ((v1_relat_1 @ sk_C)),
% 0.50/0.74      inference('demod', [status(thm)], ['8', '9'])).
% 0.50/0.74  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('139', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (~ (r1_tarski @ X0 @ sk_A)
% 0.50/0.74          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.50/0.74      inference('demod', [status(thm)], ['136', '137', '138'])).
% 0.50/0.74  thf('140', plain,
% 0.50/0.74      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.50/0.74      inference('sup-', [status(thm)], ['133', '139'])).
% 0.50/0.74  thf('141', plain,
% 0.50/0.74      ((((sk_B) != (sk_B)))
% 0.50/0.74         <= (~
% 0.50/0.74             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.50/0.74                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.50/0.74      inference('demod', [status(thm)], ['131', '132', '140'])).
% 0.50/0.74  thf('142', plain,
% 0.50/0.74      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.50/0.74          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.50/0.74      inference('simplify', [status(thm)], ['141'])).
% 0.50/0.74  thf('143', plain,
% 0.50/0.74      (~
% 0.50/0.74       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.50/0.74          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))) | 
% 0.50/0.74       ~
% 0.50/0.74       (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.50/0.74          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.50/0.74      inference('split', [status(esa)], ['125'])).
% 0.50/0.74  thf('144', plain,
% 0.50/0.74      (~
% 0.50/0.74       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.50/0.74          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.50/0.74      inference('sat_resolution*', [status(thm)], ['142', '143'])).
% 0.50/0.74  thf('145', plain,
% 0.50/0.74      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B))),
% 0.50/0.74      inference('simpl_trail', [status(thm)], ['128', '144'])).
% 0.50/0.74  thf('146', plain, ($false),
% 0.50/0.74      inference('simplify_reflect-', [status(thm)], ['118', '145'])).
% 0.50/0.74  
% 0.50/0.74  % SZS output end Refutation
% 0.50/0.74  
% 0.59/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

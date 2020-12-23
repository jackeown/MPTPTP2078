%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q8nrO6kfOj

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:26 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  229 (1137 expanded)
%              Number of leaves         :   41 ( 363 expanded)
%              Depth                    :   18
%              Number of atoms          : 1912 (19526 expanded)
%              Number of equality atoms :  114 ( 906 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X16 )
      | ( ( k10_relat_1 @ X16 @ ( k9_relat_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X13 @ ( k2_relat_1 @ X14 ) )
      | ( ( k9_relat_1 @ X14 @ ( k10_relat_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
    | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) ) )
      = ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('35',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('37',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('38',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('39',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('41',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('45',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['32','33','34','35','36','37','38','43','44'])).

thf('46',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['15','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('48',plain,(
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

thf('49',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( v3_funct_2 @ X30 @ X31 @ X32 )
      | ( v2_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('50',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('57',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('61',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('63',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X16 )
      | ( ( k10_relat_1 @ X16 @ ( k9_relat_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) )
        = X1 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) )
        = X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['61','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('68',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
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

thf('72',plain,(
    ! [X35: $i,X36: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) )
      | ~ ( v3_funct_2 @ X36 @ X35 @ X35 )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X35 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('73',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
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

thf('78',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k2_funct_2 @ X38 @ X37 )
        = ( k2_funct_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) )
      | ~ ( v3_funct_2 @ X37 @ X38 @ X38 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X38 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('79',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k2_funct_2 @ sk_A @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','83'])).

thf('85',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('86',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('88',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','83'])).

thf('90',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('91',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('93',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['88','93'])).

thf('95',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('96',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','83'])).

thf('98',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( v3_funct_2 @ X30 @ X31 @ X32 )
      | ( v2_funct_2 @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('99',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X35 @ X36 ) @ X35 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) )
      | ~ ( v3_funct_2 @ X36 @ X35 @ X35 )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X35 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('102',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( k2_funct_2 @ sk_A @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('107',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['102','103','104','105','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) )
      | ~ ( v3_funct_2 @ X36 @ X35 @ X35 )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X35 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('110',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['110','111','112','113'])).

thf('115',plain,
    ( ( k2_funct_2 @ sk_A @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('116',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['99','107','116'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('118',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v2_funct_2 @ X34 @ X33 )
      | ( ( k2_relat_1 @ X34 )
        = X33 )
      | ~ ( v5_relat_1 @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('119',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('121',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','83'])).

thf('122',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('123',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['119','120','123'])).

thf('125',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','53','54'])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( v3_funct_2 @ X30 @ X31 @ X32 )
      | ( v2_funct_2 @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('128',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v2_funct_2 @ X34 @ X33 )
      | ( ( k2_relat_1 @ X34 )
        = X33 )
      | ~ ( v5_relat_1 @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('133',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('135',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('137',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['133','134','137'])).

thf('139',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['125','138'])).

thf('140',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('141',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X18 ) @ ( k9_relat_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( v2_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['139','142'])).

thf('144',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('145',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('147',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['143','144','145','146'])).

thf('148',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('149',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['96','124','147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['70','149'])).

thf('151',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','150'])).

thf('152',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('153',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k8_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k10_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('156',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k7_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k9_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['158'])).

thf('160',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['157','159'])).

thf('161',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['154','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('163',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['158'])).

thf('164',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('166',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('168',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('171',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('172',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('173',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('175',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('176',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['169','170','171','172','173','174','175','176'])).

thf('178',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['133','134','137'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['166','179'])).

thf('181',plain,
    ( ( sk_B != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['164','165','180'])).

thf('182',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
    = sk_B ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['158'])).

thf('184',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['182','183'])).

thf('185',plain,(
    ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['161','184'])).

thf('186',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['151','185'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q8nrO6kfOj
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:47:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.62  % Solved by: fo/fo7.sh
% 0.37/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.62  % done 272 iterations in 0.157s
% 0.37/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.62  % SZS output start Refutation
% 0.37/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.62  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.37/0.62  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.37/0.62  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.37/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.62  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.37/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.62  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.37/0.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.37/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.37/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.62  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.37/0.62  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.37/0.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.37/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.37/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.62  thf(t92_funct_2, conjecture,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.37/0.62         ( v3_funct_2 @ C @ A @ A ) & 
% 0.37/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.37/0.62       ( ( r1_tarski @ B @ A ) =>
% 0.37/0.62         ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.37/0.62             ( B ) ) & 
% 0.37/0.62           ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.37/0.62             ( B ) ) ) ) ))).
% 0.37/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.62        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.37/0.62            ( v3_funct_2 @ C @ A @ A ) & 
% 0.37/0.62            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.37/0.62          ( ( r1_tarski @ B @ A ) =>
% 0.37/0.62            ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.37/0.62                ( B ) ) & 
% 0.37/0.62              ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.37/0.62                ( B ) ) ) ) ) )),
% 0.37/0.62    inference('cnf.neg', [status(esa)], [t92_funct_2])).
% 0.37/0.62  thf('0', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(d10_xboole_0, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.62  thf('1', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.37/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.62  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.62      inference('simplify', [status(thm)], ['1'])).
% 0.37/0.62  thf(d18_relat_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( v1_relat_1 @ B ) =>
% 0.37/0.62       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.37/0.62  thf('3', plain,
% 0.37/0.62      (![X5 : $i, X6 : $i]:
% 0.37/0.62         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.37/0.62          | (v4_relat_1 @ X5 @ X6)
% 0.37/0.62          | ~ (v1_relat_1 @ X5))),
% 0.37/0.62      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.37/0.62  thf('4', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.62  thf(t209_relat_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.37/0.62       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.37/0.62  thf('5', plain,
% 0.37/0.62      (![X11 : $i, X12 : $i]:
% 0.37/0.62         (((X11) = (k7_relat_1 @ X11 @ X12))
% 0.37/0.62          | ~ (v4_relat_1 @ X11 @ X12)
% 0.37/0.62          | ~ (v1_relat_1 @ X11))),
% 0.37/0.62      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.37/0.62  thf('6', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (v1_relat_1 @ X0)
% 0.37/0.62          | ~ (v1_relat_1 @ X0)
% 0.37/0.62          | ((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.62  thf('7', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 0.37/0.62      inference('simplify', [status(thm)], ['6'])).
% 0.37/0.62  thf(t148_relat_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( v1_relat_1 @ B ) =>
% 0.37/0.62       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.37/0.62  thf('8', plain,
% 0.37/0.62      (![X9 : $i, X10 : $i]:
% 0.37/0.62         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.37/0.62          | ~ (v1_relat_1 @ X9))),
% 0.37/0.62      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.37/0.62  thf('9', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.37/0.62          | ~ (v1_relat_1 @ X0)
% 0.37/0.62          | ~ (v1_relat_1 @ X0))),
% 0.37/0.62      inference('sup+', [status(thm)], ['7', '8'])).
% 0.37/0.62  thf('10', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (v1_relat_1 @ X0)
% 0.37/0.62          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.37/0.62      inference('simplify', [status(thm)], ['9'])).
% 0.37/0.62  thf('11', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.62      inference('simplify', [status(thm)], ['1'])).
% 0.37/0.62  thf(t164_funct_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.62       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.37/0.62         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.37/0.62  thf('12', plain,
% 0.37/0.62      (![X15 : $i, X16 : $i]:
% 0.37/0.62         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 0.37/0.62          | ~ (v2_funct_1 @ X16)
% 0.37/0.62          | ((k10_relat_1 @ X16 @ (k9_relat_1 @ X16 @ X15)) = (X15))
% 0.37/0.62          | ~ (v1_funct_1 @ X16)
% 0.37/0.62          | ~ (v1_relat_1 @ X16))),
% 0.37/0.62      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.37/0.62  thf('13', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (v1_relat_1 @ X0)
% 0.37/0.62          | ~ (v1_funct_1 @ X0)
% 0.37/0.62          | ((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.37/0.62              = (k1_relat_1 @ X0))
% 0.37/0.62          | ~ (v2_funct_1 @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.62  thf('14', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.37/0.62          | ~ (v1_relat_1 @ X0)
% 0.37/0.62          | ~ (v2_funct_1 @ X0)
% 0.37/0.62          | ~ (v1_funct_1 @ X0)
% 0.37/0.62          | ~ (v1_relat_1 @ X0))),
% 0.37/0.62      inference('sup+', [status(thm)], ['10', '13'])).
% 0.37/0.62  thf('15', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (v1_funct_1 @ X0)
% 0.37/0.62          | ~ (v2_funct_1 @ X0)
% 0.37/0.62          | ~ (v1_relat_1 @ X0)
% 0.37/0.62          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0)))),
% 0.37/0.62      inference('simplify', [status(thm)], ['14'])).
% 0.37/0.62  thf('16', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(cc2_relset_1, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.37/0.62  thf('17', plain,
% 0.37/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.62         ((v4_relat_1 @ X19 @ X20)
% 0.37/0.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.37/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.62  thf('18', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.37/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.62  thf('19', plain,
% 0.37/0.62      (![X11 : $i, X12 : $i]:
% 0.37/0.62         (((X11) = (k7_relat_1 @ X11 @ X12))
% 0.37/0.62          | ~ (v4_relat_1 @ X11 @ X12)
% 0.37/0.62          | ~ (v1_relat_1 @ X11))),
% 0.37/0.62      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.37/0.62  thf('20', plain,
% 0.37/0.62      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.62  thf('21', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(cc2_relat_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( v1_relat_1 @ A ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.37/0.62  thf('22', plain,
% 0.37/0.62      (![X3 : $i, X4 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.37/0.62          | (v1_relat_1 @ X3)
% 0.37/0.62          | ~ (v1_relat_1 @ X4))),
% 0.37/0.62      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.62  thf('23', plain,
% 0.37/0.62      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.37/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.62  thf(fc6_relat_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.37/0.62  thf('24', plain,
% 0.37/0.62      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.37/0.62      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.62  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.62  thf('26', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['20', '25'])).
% 0.37/0.62  thf('27', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.62      inference('simplify', [status(thm)], ['1'])).
% 0.37/0.62  thf('28', plain,
% 0.37/0.62      (![X9 : $i, X10 : $i]:
% 0.37/0.62         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.37/0.62          | ~ (v1_relat_1 @ X9))),
% 0.37/0.62      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.37/0.62  thf(t147_funct_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.62       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.37/0.62         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.37/0.62  thf('29', plain,
% 0.37/0.62      (![X13 : $i, X14 : $i]:
% 0.37/0.62         (~ (r1_tarski @ X13 @ (k2_relat_1 @ X14))
% 0.37/0.62          | ((k9_relat_1 @ X14 @ (k10_relat_1 @ X14 @ X13)) = (X13))
% 0.37/0.62          | ~ (v1_funct_1 @ X14)
% 0.37/0.62          | ~ (v1_relat_1 @ X14))),
% 0.37/0.62      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.37/0.62  thf('30', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.62         (~ (r1_tarski @ X2 @ (k9_relat_1 @ X1 @ X0))
% 0.37/0.62          | ~ (v1_relat_1 @ X1)
% 0.37/0.62          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.37/0.62          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.37/0.62          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.37/0.62              (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) = (X2)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.62  thf('31', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         (((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.37/0.62            (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0)))
% 0.37/0.62            = (k9_relat_1 @ X1 @ X0))
% 0.37/0.62          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.37/0.62          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.37/0.62          | ~ (v1_relat_1 @ X1))),
% 0.37/0.62      inference('sup-', [status(thm)], ['27', '30'])).
% 0.37/0.62  thf('32', plain,
% 0.37/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.37/0.62        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))
% 0.37/0.62        | ((k9_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 0.37/0.62            (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 0.37/0.62             (k9_relat_1 @ sk_C @ sk_A)))
% 0.37/0.62            = (k9_relat_1 @ sk_C @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['26', '31'])).
% 0.37/0.62  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.62  thf('35', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['20', '25'])).
% 0.37/0.62  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.62  thf('37', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['20', '25'])).
% 0.37/0.62  thf('38', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['20', '25'])).
% 0.37/0.62  thf('39', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['20', '25'])).
% 0.37/0.62  thf('40', plain,
% 0.37/0.62      (![X9 : $i, X10 : $i]:
% 0.37/0.62         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.37/0.62          | ~ (v1_relat_1 @ X9))),
% 0.37/0.62      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.37/0.62  thf('41', plain,
% 0.37/0.62      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.37/0.62        | ~ (v1_relat_1 @ sk_C))),
% 0.37/0.62      inference('sup+', [status(thm)], ['39', '40'])).
% 0.37/0.62  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.62  thf('43', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['41', '42'])).
% 0.37/0.62  thf('44', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['41', '42'])).
% 0.37/0.62  thf('45', plain,
% 0.37/0.62      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.37/0.62         = (k2_relat_1 @ sk_C))),
% 0.37/0.62      inference('demod', [status(thm)],
% 0.37/0.62                ['32', '33', '34', '35', '36', '37', '38', '43', '44'])).
% 0.37/0.62  thf('46', plain,
% 0.37/0.62      ((((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 0.37/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.37/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.37/0.62        | ~ (v1_funct_1 @ sk_C))),
% 0.37/0.62      inference('sup+', [status(thm)], ['15', '45'])).
% 0.37/0.62  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.62  thf('48', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(cc2_funct_2, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.62       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.37/0.62         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.37/0.62  thf('49', plain,
% 0.37/0.62      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.37/0.62         (~ (v1_funct_1 @ X30)
% 0.37/0.62          | ~ (v3_funct_2 @ X30 @ X31 @ X32)
% 0.37/0.62          | (v2_funct_1 @ X30)
% 0.37/0.62          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.37/0.62      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.37/0.62  thf('50', plain,
% 0.37/0.62      (((v2_funct_1 @ sk_C)
% 0.37/0.62        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.37/0.62        | ~ (v1_funct_1 @ sk_C))),
% 0.37/0.62      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.62  thf('51', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('53', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.62      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.37/0.62  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('55', plain,
% 0.37/0.62      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.37/0.62      inference('demod', [status(thm)], ['46', '47', '53', '54'])).
% 0.37/0.62  thf('56', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (v1_relat_1 @ X0)
% 0.37/0.62          | ~ (v1_funct_1 @ X0)
% 0.37/0.62          | ((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.37/0.62              = (k1_relat_1 @ X0))
% 0.37/0.62          | ~ (v2_funct_1 @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.62  thf('57', plain,
% 0.37/0.62      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 0.37/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.37/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.62        | ~ (v1_relat_1 @ sk_C))),
% 0.37/0.62      inference('sup+', [status(thm)], ['55', '56'])).
% 0.37/0.62  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.62      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.37/0.62  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.62  thf('61', plain,
% 0.37/0.62      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.37/0.62      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.37/0.62  thf('62', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (v1_funct_1 @ X0)
% 0.37/0.62          | ~ (v2_funct_1 @ X0)
% 0.37/0.62          | ~ (v1_relat_1 @ X0)
% 0.37/0.62          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0)))),
% 0.37/0.62      inference('simplify', [status(thm)], ['14'])).
% 0.37/0.62  thf('63', plain,
% 0.37/0.62      (![X15 : $i, X16 : $i]:
% 0.37/0.62         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 0.37/0.62          | ~ (v2_funct_1 @ X16)
% 0.37/0.62          | ((k10_relat_1 @ X16 @ (k9_relat_1 @ X16 @ X15)) = (X15))
% 0.37/0.62          | ~ (v1_funct_1 @ X16)
% 0.37/0.62          | ~ (v1_relat_1 @ X16))),
% 0.37/0.62      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.37/0.62  thf('64', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         (~ (r1_tarski @ X1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.37/0.62          | ~ (v1_relat_1 @ X0)
% 0.37/0.62          | ~ (v2_funct_1 @ X0)
% 0.37/0.62          | ~ (v1_funct_1 @ X0)
% 0.37/0.62          | ~ (v1_relat_1 @ X0)
% 0.37/0.62          | ~ (v1_funct_1 @ X0)
% 0.37/0.62          | ((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1)) = (X1))
% 0.37/0.62          | ~ (v2_funct_1 @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.62  thf('65', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         (((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1)) = (X1))
% 0.37/0.62          | ~ (v1_funct_1 @ X0)
% 0.37/0.62          | ~ (v2_funct_1 @ X0)
% 0.37/0.62          | ~ (v1_relat_1 @ X0)
% 0.37/0.62          | ~ (r1_tarski @ X1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 0.37/0.62      inference('simplify', [status(thm)], ['64'])).
% 0.37/0.62  thf('66', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_C))
% 0.37/0.62          | ~ (v1_relat_1 @ sk_C)
% 0.37/0.62          | ~ (v2_funct_1 @ sk_C)
% 0.37/0.62          | ~ (v1_funct_1 @ sk_C)
% 0.37/0.62          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['61', '65'])).
% 0.37/0.62  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.62  thf('68', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.62      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.37/0.62  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('70', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_C))
% 0.37/0.62          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.37/0.62      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.37/0.62  thf('71', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(dt_k2_funct_2, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.37/0.62         ( v3_funct_2 @ B @ A @ A ) & 
% 0.37/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.37/0.62       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.37/0.62         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.37/0.62         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.37/0.62         ( m1_subset_1 @
% 0.37/0.62           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.37/0.62  thf('72', plain,
% 0.37/0.62      (![X35 : $i, X36 : $i]:
% 0.37/0.62         ((m1_subset_1 @ (k2_funct_2 @ X35 @ X36) @ 
% 0.37/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))
% 0.37/0.62          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))
% 0.37/0.62          | ~ (v3_funct_2 @ X36 @ X35 @ X35)
% 0.37/0.62          | ~ (v1_funct_2 @ X36 @ X35 @ X35)
% 0.37/0.62          | ~ (v1_funct_1 @ X36))),
% 0.37/0.62      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.37/0.62  thf('73', plain,
% 0.37/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.62        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.37/0.62        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.37/0.62        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_C) @ 
% 0.37/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['71', '72'])).
% 0.37/0.62  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('75', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('76', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('77', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(redefinition_k2_funct_2, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.37/0.62         ( v3_funct_2 @ B @ A @ A ) & 
% 0.37/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.37/0.62       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.37/0.62  thf('78', plain,
% 0.37/0.62      (![X37 : $i, X38 : $i]:
% 0.37/0.62         (((k2_funct_2 @ X38 @ X37) = (k2_funct_1 @ X37))
% 0.37/0.62          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))
% 0.37/0.62          | ~ (v3_funct_2 @ X37 @ X38 @ X38)
% 0.37/0.62          | ~ (v1_funct_2 @ X37 @ X38 @ X38)
% 0.37/0.62          | ~ (v1_funct_1 @ X37))),
% 0.37/0.62      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.37/0.62  thf('79', plain,
% 0.37/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.62        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.37/0.62        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.37/0.62        | ((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['77', '78'])).
% 0.37/0.62  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('81', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('82', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('83', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.37/0.62      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 0.37/0.62  thf('84', plain,
% 0.37/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.62      inference('demod', [status(thm)], ['73', '74', '75', '76', '83'])).
% 0.37/0.62  thf('85', plain,
% 0.37/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.62         ((v4_relat_1 @ X19 @ X20)
% 0.37/0.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.37/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.62  thf('86', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.37/0.62      inference('sup-', [status(thm)], ['84', '85'])).
% 0.37/0.62  thf('87', plain,
% 0.37/0.62      (![X11 : $i, X12 : $i]:
% 0.37/0.62         (((X11) = (k7_relat_1 @ X11 @ X12))
% 0.37/0.62          | ~ (v4_relat_1 @ X11 @ X12)
% 0.37/0.62          | ~ (v1_relat_1 @ X11))),
% 0.37/0.62      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.37/0.62  thf('88', plain,
% 0.37/0.62      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.37/0.62        | ((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['86', '87'])).
% 0.37/0.62  thf('89', plain,
% 0.37/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.62      inference('demod', [status(thm)], ['73', '74', '75', '76', '83'])).
% 0.37/0.62  thf('90', plain,
% 0.37/0.62      (![X3 : $i, X4 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.37/0.62          | (v1_relat_1 @ X3)
% 0.37/0.62          | ~ (v1_relat_1 @ X4))),
% 0.37/0.62      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.62  thf('91', plain,
% 0.37/0.62      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 0.37/0.62        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['89', '90'])).
% 0.37/0.62  thf('92', plain,
% 0.37/0.62      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.37/0.62      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.62  thf('93', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.37/0.62      inference('demod', [status(thm)], ['91', '92'])).
% 0.37/0.62  thf('94', plain,
% 0.37/0.62      (((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['88', '93'])).
% 0.37/0.62  thf('95', plain,
% 0.37/0.62      (![X9 : $i, X10 : $i]:
% 0.37/0.62         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.37/0.62          | ~ (v1_relat_1 @ X9))),
% 0.37/0.62      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.37/0.62  thf('96', plain,
% 0.37/0.62      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.37/0.62          = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))
% 0.37/0.62        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['94', '95'])).
% 0.37/0.62  thf('97', plain,
% 0.37/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.62      inference('demod', [status(thm)], ['73', '74', '75', '76', '83'])).
% 0.37/0.62  thf('98', plain,
% 0.37/0.62      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.37/0.62         (~ (v1_funct_1 @ X30)
% 0.37/0.62          | ~ (v3_funct_2 @ X30 @ X31 @ X32)
% 0.37/0.62          | (v2_funct_2 @ X30 @ X32)
% 0.37/0.62          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.37/0.62      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.37/0.62  thf('99', plain,
% 0.37/0.62      (((v2_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A)
% 0.37/0.62        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)
% 0.37/0.62        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['97', '98'])).
% 0.37/0.62  thf('100', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('101', plain,
% 0.37/0.62      (![X35 : $i, X36 : $i]:
% 0.37/0.62         ((v3_funct_2 @ (k2_funct_2 @ X35 @ X36) @ X35 @ X35)
% 0.37/0.62          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))
% 0.37/0.62          | ~ (v3_funct_2 @ X36 @ X35 @ X35)
% 0.37/0.62          | ~ (v1_funct_2 @ X36 @ X35 @ X35)
% 0.37/0.62          | ~ (v1_funct_1 @ X36))),
% 0.37/0.62      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.37/0.62  thf('102', plain,
% 0.37/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.62        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.37/0.62        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.37/0.62        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['100', '101'])).
% 0.37/0.62  thf('103', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('104', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('105', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('106', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.37/0.62      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 0.37/0.62  thf('107', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)),
% 0.37/0.62      inference('demod', [status(thm)], ['102', '103', '104', '105', '106'])).
% 0.37/0.62  thf('108', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('109', plain,
% 0.37/0.62      (![X35 : $i, X36 : $i]:
% 0.37/0.62         ((v1_funct_1 @ (k2_funct_2 @ X35 @ X36))
% 0.37/0.62          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))
% 0.37/0.62          | ~ (v3_funct_2 @ X36 @ X35 @ X35)
% 0.37/0.62          | ~ (v1_funct_2 @ X36 @ X35 @ X35)
% 0.37/0.62          | ~ (v1_funct_1 @ X36))),
% 0.37/0.62      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.37/0.62  thf('110', plain,
% 0.37/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.62        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.37/0.62        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.37/0.62        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_C)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['108', '109'])).
% 0.37/0.62  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('112', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('113', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('114', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_C))),
% 0.37/0.62      inference('demod', [status(thm)], ['110', '111', '112', '113'])).
% 0.37/0.62  thf('115', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.37/0.62      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 0.37/0.62  thf('116', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.37/0.62      inference('demod', [status(thm)], ['114', '115'])).
% 0.37/0.62  thf('117', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.37/0.62      inference('demod', [status(thm)], ['99', '107', '116'])).
% 0.37/0.62  thf(d3_funct_2, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.37/0.62       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.37/0.62  thf('118', plain,
% 0.37/0.62      (![X33 : $i, X34 : $i]:
% 0.37/0.62         (~ (v2_funct_2 @ X34 @ X33)
% 0.37/0.62          | ((k2_relat_1 @ X34) = (X33))
% 0.37/0.62          | ~ (v5_relat_1 @ X34 @ X33)
% 0.37/0.62          | ~ (v1_relat_1 @ X34))),
% 0.37/0.62      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.37/0.62  thf('119', plain,
% 0.37/0.62      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.37/0.62        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)
% 0.37/0.62        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['117', '118'])).
% 0.37/0.62  thf('120', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.37/0.62      inference('demod', [status(thm)], ['91', '92'])).
% 0.37/0.62  thf('121', plain,
% 0.37/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.62      inference('demod', [status(thm)], ['73', '74', '75', '76', '83'])).
% 0.37/0.62  thf('122', plain,
% 0.37/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.62         ((v5_relat_1 @ X19 @ X21)
% 0.37/0.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.37/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.62  thf('123', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.37/0.62      inference('sup-', [status(thm)], ['121', '122'])).
% 0.37/0.62  thf('124', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['119', '120', '123'])).
% 0.37/0.62  thf('125', plain,
% 0.37/0.62      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.37/0.62      inference('demod', [status(thm)], ['46', '47', '53', '54'])).
% 0.37/0.62  thf('126', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('127', plain,
% 0.37/0.62      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.37/0.62         (~ (v1_funct_1 @ X30)
% 0.37/0.62          | ~ (v3_funct_2 @ X30 @ X31 @ X32)
% 0.37/0.62          | (v2_funct_2 @ X30 @ X32)
% 0.37/0.62          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.37/0.62      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.37/0.62  thf('128', plain,
% 0.37/0.62      (((v2_funct_2 @ sk_C @ sk_A)
% 0.37/0.62        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.37/0.62        | ~ (v1_funct_1 @ sk_C))),
% 0.37/0.62      inference('sup-', [status(thm)], ['126', '127'])).
% 0.37/0.62  thf('129', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('130', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('131', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.37/0.62      inference('demod', [status(thm)], ['128', '129', '130'])).
% 0.37/0.62  thf('132', plain,
% 0.37/0.62      (![X33 : $i, X34 : $i]:
% 0.37/0.62         (~ (v2_funct_2 @ X34 @ X33)
% 0.37/0.62          | ((k2_relat_1 @ X34) = (X33))
% 0.37/0.62          | ~ (v5_relat_1 @ X34 @ X33)
% 0.37/0.62          | ~ (v1_relat_1 @ X34))),
% 0.37/0.62      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.37/0.62  thf('133', plain,
% 0.37/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.62        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.37/0.62        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['131', '132'])).
% 0.37/0.62  thf('134', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.62  thf('135', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('136', plain,
% 0.37/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.62         ((v5_relat_1 @ X19 @ X21)
% 0.37/0.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.37/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.62  thf('137', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.37/0.62      inference('sup-', [status(thm)], ['135', '136'])).
% 0.37/0.62  thf('138', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['133', '134', '137'])).
% 0.37/0.62  thf('139', plain, (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['125', '138'])).
% 0.37/0.62  thf('140', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.62      inference('simplify', [status(thm)], ['1'])).
% 0.37/0.62  thf(t177_funct_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.37/0.62           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 0.37/0.62             ( B ) ) ) ) ))).
% 0.37/0.62  thf('141', plain,
% 0.37/0.62      (![X17 : $i, X18 : $i]:
% 0.37/0.62         (~ (r1_tarski @ X17 @ (k1_relat_1 @ X18))
% 0.37/0.62          | ((k9_relat_1 @ (k2_funct_1 @ X18) @ (k9_relat_1 @ X18 @ X17))
% 0.37/0.62              = (X17))
% 0.37/0.62          | ~ (v2_funct_1 @ X18)
% 0.37/0.62          | ~ (v1_funct_1 @ X18)
% 0.37/0.62          | ~ (v1_relat_1 @ X18))),
% 0.37/0.62      inference('cnf', [status(esa)], [t177_funct_1])).
% 0.37/0.62  thf('142', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (v1_relat_1 @ X0)
% 0.37/0.62          | ~ (v1_funct_1 @ X0)
% 0.37/0.62          | ~ (v2_funct_1 @ X0)
% 0.37/0.62          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.37/0.62              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['140', '141'])).
% 0.37/0.62  thf('143', plain,
% 0.37/0.62      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A) = (k1_relat_1 @ sk_C))
% 0.37/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.37/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.62        | ~ (v1_relat_1 @ sk_C))),
% 0.37/0.62      inference('sup+', [status(thm)], ['139', '142'])).
% 0.37/0.62  thf('144', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.62      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.37/0.62  thf('145', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('146', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.62  thf('147', plain,
% 0.37/0.62      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.37/0.62      inference('demod', [status(thm)], ['143', '144', '145', '146'])).
% 0.37/0.62  thf('148', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.37/0.62      inference('demod', [status(thm)], ['91', '92'])).
% 0.37/0.62  thf('149', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.37/0.62      inference('demod', [status(thm)], ['96', '124', '147', '148'])).
% 0.37/0.62  thf('150', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (r1_tarski @ X0 @ sk_A)
% 0.37/0.62          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.37/0.62      inference('demod', [status(thm)], ['70', '149'])).
% 0.37/0.62  thf('151', plain,
% 0.37/0.62      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['0', '150'])).
% 0.37/0.62  thf('152', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(redefinition_k8_relset_1, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.62       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.37/0.62  thf('153', plain,
% 0.37/0.62      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.37/0.62          | ((k8_relset_1 @ X27 @ X28 @ X26 @ X29) = (k10_relat_1 @ X26 @ X29)))),
% 0.37/0.62      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.37/0.62  thf('154', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['152', '153'])).
% 0.37/0.62  thf('155', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(redefinition_k7_relset_1, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.62       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.37/0.62  thf('156', plain,
% 0.37/0.62      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.37/0.62          | ((k7_relset_1 @ X23 @ X24 @ X22 @ X25) = (k9_relat_1 @ X22 @ X25)))),
% 0.37/0.62      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.37/0.62  thf('157', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['155', '156'])).
% 0.37/0.62  thf('158', plain,
% 0.37/0.62      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.37/0.62          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B))
% 0.37/0.62        | ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.37/0.62            (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('159', plain,
% 0.37/0.62      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.37/0.62          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.37/0.62         <= (~
% 0.37/0.62             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.37/0.62                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.37/0.62      inference('split', [status(esa)], ['158'])).
% 0.37/0.62  thf('160', plain,
% 0.37/0.62      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.37/0.62          != (sk_B)))
% 0.37/0.62         <= (~
% 0.37/0.62             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.37/0.62                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['157', '159'])).
% 0.37/0.62  thf('161', plain,
% 0.37/0.62      ((((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B)))
% 0.37/0.62         <= (~
% 0.37/0.62             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.37/0.62                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['154', '160'])).
% 0.37/0.62  thf('162', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['152', '153'])).
% 0.37/0.62  thf('163', plain,
% 0.37/0.62      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.37/0.62          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.37/0.62         <= (~
% 0.37/0.62             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.37/0.62                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.37/0.62      inference('split', [status(esa)], ['158'])).
% 0.37/0.62  thf('164', plain,
% 0.37/0.62      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ (k10_relat_1 @ sk_C @ sk_B))
% 0.37/0.62          != (sk_B)))
% 0.37/0.62         <= (~
% 0.37/0.62             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.37/0.62                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['162', '163'])).
% 0.37/0.62  thf('165', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['155', '156'])).
% 0.37/0.62  thf('166', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('167', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['41', '42'])).
% 0.37/0.62  thf('168', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.62         (~ (r1_tarski @ X2 @ (k9_relat_1 @ X1 @ X0))
% 0.37/0.62          | ~ (v1_relat_1 @ X1)
% 0.37/0.62          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.37/0.62          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.37/0.62          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.37/0.62              (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) = (X2)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.62  thf('169', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (r1_tarski @ X0 @ (k2_relat_1 @ sk_C))
% 0.37/0.62          | ((k9_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 0.37/0.62              (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ X0)) = (X0))
% 0.37/0.62          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ sk_A))
% 0.37/0.62          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))
% 0.37/0.62          | ~ (v1_relat_1 @ sk_C))),
% 0.37/0.62      inference('sup-', [status(thm)], ['167', '168'])).
% 0.37/0.62  thf('170', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['20', '25'])).
% 0.37/0.62  thf('171', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['20', '25'])).
% 0.37/0.62  thf('172', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['20', '25'])).
% 0.37/0.62  thf('173', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('174', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['20', '25'])).
% 0.37/0.62  thf('175', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.62  thf('176', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.62  thf('177', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (r1_tarski @ X0 @ (k2_relat_1 @ sk_C))
% 0.37/0.62          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.37/0.62      inference('demod', [status(thm)],
% 0.37/0.62                ['169', '170', '171', '172', '173', '174', '175', '176'])).
% 0.37/0.62  thf('178', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['133', '134', '137'])).
% 0.37/0.62  thf('179', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (r1_tarski @ X0 @ sk_A)
% 0.37/0.62          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.37/0.62      inference('demod', [status(thm)], ['177', '178'])).
% 0.37/0.62  thf('180', plain,
% 0.37/0.62      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['166', '179'])).
% 0.37/0.62  thf('181', plain,
% 0.37/0.62      ((((sk_B) != (sk_B)))
% 0.37/0.62         <= (~
% 0.37/0.62             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.37/0.62                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.37/0.62      inference('demod', [status(thm)], ['164', '165', '180'])).
% 0.37/0.62  thf('182', plain,
% 0.37/0.62      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.37/0.62          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.37/0.62      inference('simplify', [status(thm)], ['181'])).
% 0.37/0.62  thf('183', plain,
% 0.37/0.62      (~
% 0.37/0.62       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.37/0.62          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))) | 
% 0.37/0.62       ~
% 0.37/0.62       (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.37/0.62          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.37/0.62      inference('split', [status(esa)], ['158'])).
% 0.37/0.62  thf('184', plain,
% 0.37/0.62      (~
% 0.37/0.62       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.37/0.62          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.37/0.62      inference('sat_resolution*', [status(thm)], ['182', '183'])).
% 0.37/0.62  thf('185', plain,
% 0.37/0.62      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B))),
% 0.37/0.62      inference('simpl_trail', [status(thm)], ['161', '184'])).
% 0.37/0.62  thf('186', plain, ($false),
% 0.37/0.62      inference('simplify_reflect-', [status(thm)], ['151', '185'])).
% 0.37/0.62  
% 0.37/0.62  % SZS output end Refutation
% 0.37/0.62  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

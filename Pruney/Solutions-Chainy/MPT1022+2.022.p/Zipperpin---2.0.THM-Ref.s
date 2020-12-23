%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fyMNYsxEGP

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 520 expanded)
%              Number of leaves         :   39 ( 175 expanded)
%              Depth                    :   16
%              Number of atoms          : 1181 (8071 expanded)
%              Number of equality atoms :   88 ( 391 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

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

thf(t39_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
          = ( k2_relset_1 @ B @ A @ C ) )
        & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
          = ( k1_relset_1 @ B @ A @ C ) ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k8_relset_1 @ X24 @ X25 @ X26 @ ( k7_relset_1 @ X24 @ X25 @ X26 @ X24 ) )
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[t39_relset_1])).

thf('3',plain,
    ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_A ) )
    = ( k1_relset_1 @ sk_A @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( ( k7_relset_1 @ X17 @ X18 @ X16 @ X19 )
        = ( k9_relat_1 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('9',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['11','16'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('19',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('21',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_1 @ X27 )
      | ~ ( v3_funct_2 @ X27 @ X28 @ X29 )
      | ( v2_funct_2 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('24',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('28',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v2_funct_2 @ X31 @ X30 )
      | ( ( k2_relat_1 @ X31 )
        = X30 )
      | ~ ( v5_relat_1 @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('33',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['29','30','33'])).

thf('35',plain,
    ( sk_A
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['21','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k8_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k10_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('40',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X32 @ X33 )
        = X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X32 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('41',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['3','6','35','38','44'])).

thf('46',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('47',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X6: $i] :
      ( ( ( k10_relat_1 @ X6 @ ( k2_relat_1 @ X6 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('53',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('54',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('55',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('56',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('57',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['29','30','33'])).

thf('59',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['45','59'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('61',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ ( k1_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ( ( k10_relat_1 @ X12 @ ( k9_relat_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_1 @ X27 )
      | ~ ( v3_funct_2 @ X27 @ X28 @ X29 )
      | ( v2_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('67',plain,
    ( ( v2_funct_1 @ sk_C )
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
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['62','63','64','70'])).

thf('72',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','71'])).

thf('73',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('77',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('80',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('81',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X9 @ ( k2_relat_1 @ X10 ) )
      | ( ( k9_relat_1 @ X10 @ ( k10_relat_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('85',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('86',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('87',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('89',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('90',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87','88','89','90'])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['29','30','33'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['78','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('97',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['73'])).

thf('98',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,
    ( ( sk_B != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['94','99'])).

thf('101',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
    = sk_B ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['73'])).

thf('103',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['101','102'])).

thf('104',plain,(
    ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['77','103'])).

thf('105',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['72','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fyMNYsxEGP
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:57:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 66 iterations in 0.029s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.49  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.49  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.49  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.49  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(t92_funct_2, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.20/0.49         ( v3_funct_2 @ C @ A @ A ) & 
% 0.20/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.49       ( ( r1_tarski @ B @ A ) =>
% 0.20/0.49         ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.20/0.49             ( B ) ) & 
% 0.20/0.49           ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.20/0.49             ( B ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.49        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.20/0.49            ( v3_funct_2 @ C @ A @ A ) & 
% 0.20/0.49            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.49          ( ( r1_tarski @ B @ A ) =>
% 0.20/0.49            ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.20/0.49                ( B ) ) & 
% 0.20/0.49              ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.20/0.49                ( B ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t92_funct_2])).
% 0.20/0.49  thf('0', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t39_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.49       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.20/0.49           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.20/0.49         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.20/0.49           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.49         (((k8_relset_1 @ X24 @ X25 @ X26 @ 
% 0.20/0.49            (k7_relset_1 @ X24 @ X25 @ X26 @ X24))
% 0.20/0.49            = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.20/0.49          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.20/0.49      inference('cnf', [status(esa)], [t39_relset_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.49         (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_A))
% 0.20/0.49         = (k1_relset_1 @ sk_A @ sk_A @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.20/0.49          | ((k7_relset_1 @ X17 @ X18 @ X16 @ X19) = (k9_relat_1 @ X16 @ X19)))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc2_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.49         ((v4_relat_1 @ X13 @ X14)
% 0.20/0.49          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.49  thf('9', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf(t209_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.49       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]:
% 0.20/0.49         (((X7) = (k7_relat_1 @ X7 @ X8))
% 0.20/0.49          | ~ (v4_relat_1 @ X7 @ X8)
% 0.20/0.49          | ~ (v1_relat_1 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc2_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.49          | (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf(fc6_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.49  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('17', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '16'])).
% 0.20/0.49  thf(t148_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i]:
% 0.20/0.49         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.20/0.49          | ~ (v1_relat_1 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.49      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('21', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc2_funct_2, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.20/0.49         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.49         (~ (v1_funct_1 @ X27)
% 0.20/0.49          | ~ (v3_funct_2 @ X27 @ X28 @ X29)
% 0.20/0.49          | (v2_funct_2 @ X27 @ X29)
% 0.20/0.49          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (((v2_funct_2 @ sk_C @ sk_A)
% 0.20/0.49        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('27', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.20/0.49  thf(d3_funct_2, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.20/0.49       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X30 : $i, X31 : $i]:
% 0.20/0.49         (~ (v2_funct_2 @ X31 @ X30)
% 0.20/0.49          | ((k2_relat_1 @ X31) = (X30))
% 0.20/0.49          | ~ (v5_relat_1 @ X31 @ X30)
% 0.20/0.49          | ~ (v1_relat_1 @ X31))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.49        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.20/0.49        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.49         ((v5_relat_1 @ X13 @ X15)
% 0.20/0.49          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.49  thf('33', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.49  thf('34', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['29', '30', '33'])).
% 0.20/0.49  thf('35', plain, (((sk_A) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['21', '34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.20/0.49          | ((k8_relset_1 @ X21 @ X22 @ X20 @ X23) = (k10_relat_1 @ X20 @ X23)))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t67_funct_2, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.49         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.49       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X32 : $i, X33 : $i]:
% 0.20/0.49         (((k1_relset_1 @ X32 @ X32 @ X33) = (X32))
% 0.20/0.49          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))
% 0.20/0.49          | ~ (v1_funct_2 @ X33 @ X32 @ X32)
% 0.20/0.49          | ~ (v1_funct_1 @ X33))),
% 0.20/0.49      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      ((~ (v1_funct_1 @ sk_C)
% 0.20/0.49        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.20/0.49        | ((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.49  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('43', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('44', plain, (((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.20/0.49  thf('45', plain, (((k10_relat_1 @ sk_C @ sk_A) = (sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['3', '6', '35', '38', '44'])).
% 0.20/0.49  thf('46', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '16'])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i]:
% 0.20/0.49         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.20/0.49          | ~ (v1_relat_1 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.49  thf(t169_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (![X6 : $i]:
% 0.20/0.49         (((k10_relat_1 @ X6 @ (k2_relat_1 @ X6)) = (k1_relat_1 @ X6))
% 0.20/0.49          | ~ (v1_relat_1 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.20/0.49            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['47', '48'])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.49        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.49        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 0.20/0.49            (k9_relat_1 @ sk_C @ sk_A))
% 0.20/0.49            = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['46', '49'])).
% 0.20/0.49  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('53', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '16'])).
% 0.20/0.49  thf('54', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '16'])).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (k1_relat_1 @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.20/0.49  thf('56', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.49  thf('58', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['29', '30', '33'])).
% 0.20/0.49  thf('59', plain, (((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.49  thf('60', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.49      inference('sup+', [status(thm)], ['45', '59'])).
% 0.20/0.49  thf(t164_funct_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.20/0.49         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.20/0.49  thf('61', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X11 @ (k1_relat_1 @ X12))
% 0.20/0.49          | ~ (v2_funct_1 @ X12)
% 0.20/0.49          | ((k10_relat_1 @ X12 @ (k9_relat_1 @ X12 @ X11)) = (X11))
% 0.20/0.49          | ~ (v1_funct_1 @ X12)
% 0.20/0.49          | ~ (v1_relat_1 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.20/0.49  thf('62', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X0 @ sk_A)
% 0.20/0.49          | ~ (v1_relat_1 @ sk_C)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.49          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0))
% 0.20/0.49          | ~ (v2_funct_1 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.49  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('65', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('66', plain,
% 0.20/0.49      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.49         (~ (v1_funct_1 @ X27)
% 0.20/0.49          | ~ (v3_funct_2 @ X27 @ X28 @ X29)
% 0.20/0.49          | (v2_funct_1 @ X27)
% 0.20/0.49          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.20/0.49  thf('67', plain,
% 0.20/0.49      (((v2_funct_1 @ sk_C)
% 0.20/0.49        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.49  thf('68', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('70', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.20/0.49  thf('71', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X0 @ sk_A)
% 0.20/0.49          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['62', '63', '64', '70'])).
% 0.20/0.49  thf('72', plain,
% 0.20/0.49      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '71'])).
% 0.20/0.49  thf('73', plain,
% 0.20/0.49      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.49          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B))
% 0.20/0.49        | ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.49            (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('74', plain,
% 0.20/0.49      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.49          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.49                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['73'])).
% 0.20/0.49  thf('75', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('76', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.49  thf('77', plain,
% 0.20/0.49      ((((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.49                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.20/0.49      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.20/0.49  thf('78', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('79', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('80', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i]:
% 0.20/0.49         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.20/0.49          | ~ (v1_relat_1 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.49  thf(t147_funct_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.20/0.49         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.20/0.49  thf('81', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X9 @ (k2_relat_1 @ X10))
% 0.20/0.49          | ((k9_relat_1 @ X10 @ (k10_relat_1 @ X10 @ X9)) = (X9))
% 0.20/0.49          | ~ (v1_funct_1 @ X10)
% 0.20/0.49          | ~ (v1_relat_1 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.20/0.49  thf('82', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X2 @ (k9_relat_1 @ X1 @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.49          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.49          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.20/0.49              (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) = (X2)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['80', '81'])).
% 0.20/0.49  thf('83', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X0 @ (k2_relat_1 @ sk_C))
% 0.20/0.49          | ((k9_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 0.20/0.49              (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ X0)) = (X0))
% 0.20/0.49          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ sk_A))
% 0.20/0.49          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))
% 0.20/0.49          | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['79', '82'])).
% 0.20/0.49  thf('84', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '16'])).
% 0.20/0.49  thf('85', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '16'])).
% 0.20/0.49  thf('86', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '16'])).
% 0.20/0.49  thf('87', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('88', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '16'])).
% 0.20/0.49  thf('89', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('90', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('91', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X0 @ (k2_relat_1 @ sk_C))
% 0.20/0.49          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.20/0.49      inference('demod', [status(thm)],
% 0.20/0.49                ['83', '84', '85', '86', '87', '88', '89', '90'])).
% 0.20/0.49  thf('92', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['29', '30', '33'])).
% 0.20/0.49  thf('93', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X0 @ sk_A)
% 0.20/0.49          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['91', '92'])).
% 0.20/0.49  thf('94', plain,
% 0.20/0.49      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['78', '93'])).
% 0.20/0.49  thf('95', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.49  thf('96', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('97', plain,
% 0.20/0.49      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.49          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.49                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['73'])).
% 0.20/0.49  thf('98', plain,
% 0.20/0.49      ((((k9_relat_1 @ sk_C @ (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B))
% 0.20/0.49          != (sk_B)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.49                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['96', '97'])).
% 0.20/0.49  thf('99', plain,
% 0.20/0.49      ((((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) != (sk_B)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.49                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['95', '98'])).
% 0.20/0.49  thf('100', plain,
% 0.20/0.49      ((((sk_B) != (sk_B)))
% 0.20/0.49         <= (~
% 0.20/0.49             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.49                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['94', '99'])).
% 0.20/0.49  thf('101', plain,
% 0.20/0.49      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.49          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['100'])).
% 0.20/0.49  thf('102', plain,
% 0.20/0.49      (~
% 0.20/0.49       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.49          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))) | 
% 0.20/0.49       ~
% 0.20/0.49       (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.49          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['73'])).
% 0.20/0.49  thf('103', plain,
% 0.20/0.49      (~
% 0.20/0.49       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.49          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['101', '102'])).
% 0.20/0.49  thf('104', plain,
% 0.20/0.49      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['77', '103'])).
% 0.20/0.49  thf('105', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['72', '104'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

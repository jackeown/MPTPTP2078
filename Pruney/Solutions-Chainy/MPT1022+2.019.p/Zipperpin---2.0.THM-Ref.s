%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TESFbkmCUc

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:27 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 748 expanded)
%              Number of leaves         :   40 ( 246 expanded)
%              Depth                    :   16
%              Number of atoms          : 1552 (13939 expanded)
%              Number of equality atoms :   92 ( 630 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

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

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k10_relat_1 @ X11 @ X12 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X11 ) @ X12 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X31: $i,X32: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v3_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('4',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_funct_2 @ X34 @ X33 )
        = ( k2_funct_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) )
      | ~ ( v3_funct_2 @ X33 @ X34 @ X34 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X34 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('10',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_funct_2 @ sk_A @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','14'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v4_relat_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','14'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('24',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['19','24'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('27',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','14'])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('29',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X28 )
      | ( v2_funct_2 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('30',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X31 @ X32 ) @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v3_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k2_funct_2 @ sk_A @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('38',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['33','34','35','36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v3_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('41',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,
    ( ( k2_funct_2 @ sk_A @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('47',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['30','38','47'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('49',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v2_funct_2 @ X30 @ X29 )
      | ( ( k2_relat_1 @ X30 )
        = X29 )
      | ~ ( v5_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('52',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','14'])).

thf('53',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('54',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['50','51','54'])).

thf('56',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('57',plain,
    ( sk_A
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['27','55','56'])).

thf('58',plain,
    ( ( sk_A
      = ( k10_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v4_relat_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('61',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('68',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['63','68'])).

thf('70',plain,(
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

thf('71',plain,(
    ! [X6: $i] :
      ( ( ( k10_relat_1 @ X6 @ ( k2_relat_1 @ X6 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['66','67'])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['66','67'])).

thf('76',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['63','68'])).

thf('77',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['63','68'])).

thf('78',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['63','68'])).

thf('80',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('81',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['66','67'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X28 )
      | ( v2_funct_2 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('87',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v2_funct_2 @ X30 @ X29 )
      | ( ( k2_relat_1 @ X30 )
        = X29 )
      | ~ ( v5_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('92',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['66','67'])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('96',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['92','93','96'])).

thf('98',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['84','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['66','67'])).

thf('100',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X28 )
      | ( v2_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('103',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['58','98','99','100','106'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('108',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X13 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v2_funct_1 @ X14 )
      | ( ( k10_relat_1 @ X14 @ ( k9_relat_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['66','67'])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['109','110','111','112'])).

thf('114',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','113'])).

thf('115',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['115'])).

thf('117',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('118',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k7_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k9_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('121',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k8_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k10_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['116','119','122'])).

thf('124',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('126',plain,(
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

thf('127',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X9 @ ( k2_relat_1 @ X10 ) )
      | ( ( k9_relat_1 @ X10 @ ( k10_relat_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['125','128'])).

thf('130',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['63','68'])).

thf('131',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['63','68'])).

thf('132',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['63','68'])).

thf('133',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['63','68'])).

thf('135',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['66','67'])).

thf('136',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['66','67'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['129','130','131','132','133','134','135','136'])).

thf('138',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['92','93','96'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['124','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('143',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['115'])).

thf('144',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['141','144'])).

thf('146',plain,
    ( ( sk_B != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['140','145'])).

thf('147',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
    = sk_B ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['115'])).

thf('149',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['147','148'])).

thf('150',plain,(
    ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['123','149'])).

thf('151',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['114','150'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TESFbkmCUc
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:23:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.59/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.76  % Solved by: fo/fo7.sh
% 0.59/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.76  % done 157 iterations in 0.310s
% 0.59/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.76  % SZS output start Refutation
% 0.59/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.76  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.59/0.76  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.59/0.76  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.59/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.76  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.59/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.76  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.59/0.76  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.59/0.76  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.59/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.76  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.59/0.76  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.59/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.76  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.59/0.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.76  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.59/0.76  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.59/0.76  thf(t92_funct_2, conjecture,
% 0.59/0.76    (![A:$i,B:$i,C:$i]:
% 0.59/0.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.59/0.76         ( v3_funct_2 @ C @ A @ A ) & 
% 0.59/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.59/0.76       ( ( r1_tarski @ B @ A ) =>
% 0.59/0.76         ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.59/0.76             ( B ) ) & 
% 0.59/0.76           ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.59/0.76             ( B ) ) ) ) ))).
% 0.59/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.76    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.76        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.59/0.76            ( v3_funct_2 @ C @ A @ A ) & 
% 0.59/0.76            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.59/0.76          ( ( r1_tarski @ B @ A ) =>
% 0.59/0.76            ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.59/0.76                ( B ) ) & 
% 0.59/0.76              ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.59/0.76                ( B ) ) ) ) ) )),
% 0.59/0.76    inference('cnf.neg', [status(esa)], [t92_funct_2])).
% 0.59/0.76  thf('0', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(t155_funct_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.76       ( ( v2_funct_1 @ B ) =>
% 0.59/0.76         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.59/0.76  thf('1', plain,
% 0.59/0.76      (![X11 : $i, X12 : $i]:
% 0.59/0.76         (~ (v2_funct_1 @ X11)
% 0.59/0.76          | ((k10_relat_1 @ X11 @ X12)
% 0.59/0.76              = (k9_relat_1 @ (k2_funct_1 @ X11) @ X12))
% 0.59/0.76          | ~ (v1_funct_1 @ X11)
% 0.59/0.76          | ~ (v1_relat_1 @ X11))),
% 0.59/0.76      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.59/0.76  thf('2', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(dt_k2_funct_2, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.59/0.76         ( v3_funct_2 @ B @ A @ A ) & 
% 0.59/0.76         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.59/0.76       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.59/0.76         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.59/0.76         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.59/0.76         ( m1_subset_1 @
% 0.59/0.76           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.59/0.76  thf('3', plain,
% 0.59/0.76      (![X31 : $i, X32 : $i]:
% 0.59/0.76         ((m1_subset_1 @ (k2_funct_2 @ X31 @ X32) @ 
% 0.59/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 0.59/0.76          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 0.59/0.76          | ~ (v3_funct_2 @ X32 @ X31 @ X31)
% 0.59/0.76          | ~ (v1_funct_2 @ X32 @ X31 @ X31)
% 0.59/0.76          | ~ (v1_funct_1 @ X32))),
% 0.59/0.76      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.59/0.76  thf('4', plain,
% 0.59/0.76      ((~ (v1_funct_1 @ sk_C)
% 0.59/0.76        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.59/0.76        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.59/0.76        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_C) @ 
% 0.59/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.59/0.76      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.76  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('6', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('7', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('8', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(redefinition_k2_funct_2, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.59/0.76         ( v3_funct_2 @ B @ A @ A ) & 
% 0.59/0.76         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.59/0.76       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.59/0.76  thf('9', plain,
% 0.59/0.76      (![X33 : $i, X34 : $i]:
% 0.59/0.76         (((k2_funct_2 @ X34 @ X33) = (k2_funct_1 @ X33))
% 0.59/0.76          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))
% 0.59/0.76          | ~ (v3_funct_2 @ X33 @ X34 @ X34)
% 0.59/0.76          | ~ (v1_funct_2 @ X33 @ X34 @ X34)
% 0.59/0.76          | ~ (v1_funct_1 @ X33))),
% 0.59/0.76      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.59/0.76  thf('10', plain,
% 0.59/0.76      ((~ (v1_funct_1 @ sk_C)
% 0.59/0.76        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.59/0.76        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.59/0.76        | ((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.76  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('12', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('13', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('14', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.59/0.76  thf('15', plain,
% 0.59/0.76      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.76      inference('demod', [status(thm)], ['4', '5', '6', '7', '14'])).
% 0.59/0.76  thf(cc2_relset_1, axiom,
% 0.59/0.76    (![A:$i,B:$i,C:$i]:
% 0.59/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.76       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.59/0.76  thf('16', plain,
% 0.59/0.76      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.76         ((v4_relat_1 @ X15 @ X16)
% 0.59/0.76          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.59/0.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.59/0.76  thf('17', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.59/0.76      inference('sup-', [status(thm)], ['15', '16'])).
% 0.59/0.76  thf(t209_relat_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.59/0.76       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.59/0.76  thf('18', plain,
% 0.59/0.76      (![X7 : $i, X8 : $i]:
% 0.59/0.76         (((X7) = (k7_relat_1 @ X7 @ X8))
% 0.59/0.76          | ~ (v4_relat_1 @ X7 @ X8)
% 0.59/0.76          | ~ (v1_relat_1 @ X7))),
% 0.59/0.76      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.59/0.76  thf('19', plain,
% 0.59/0.76      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.59/0.76        | ((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['17', '18'])).
% 0.59/0.76  thf('20', plain,
% 0.59/0.76      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.76      inference('demod', [status(thm)], ['4', '5', '6', '7', '14'])).
% 0.59/0.76  thf(cc2_relat_1, axiom,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( v1_relat_1 @ A ) =>
% 0.59/0.76       ( ![B:$i]:
% 0.59/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.59/0.76  thf('21', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.59/0.76          | (v1_relat_1 @ X0)
% 0.59/0.76          | ~ (v1_relat_1 @ X1))),
% 0.59/0.76      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.59/0.76  thf('22', plain,
% 0.59/0.76      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 0.59/0.76        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.76  thf(fc6_relat_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.59/0.76  thf('23', plain,
% 0.59/0.76      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.59/0.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.59/0.76  thf('24', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['22', '23'])).
% 0.59/0.76  thf('25', plain,
% 0.59/0.76      (((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))),
% 0.59/0.76      inference('demod', [status(thm)], ['19', '24'])).
% 0.59/0.76  thf(t148_relat_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( v1_relat_1 @ B ) =>
% 0.59/0.76       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.59/0.76  thf('26', plain,
% 0.59/0.76      (![X4 : $i, X5 : $i]:
% 0.59/0.76         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.59/0.76          | ~ (v1_relat_1 @ X4))),
% 0.59/0.76      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.59/0.76  thf('27', plain,
% 0.59/0.76      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.59/0.76          = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))
% 0.59/0.76        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.59/0.76      inference('sup+', [status(thm)], ['25', '26'])).
% 0.59/0.76  thf('28', plain,
% 0.59/0.76      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.76      inference('demod', [status(thm)], ['4', '5', '6', '7', '14'])).
% 0.59/0.76  thf(cc2_funct_2, axiom,
% 0.59/0.76    (![A:$i,B:$i,C:$i]:
% 0.59/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.76       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.59/0.76         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.59/0.76  thf('29', plain,
% 0.59/0.76      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.59/0.76         (~ (v1_funct_1 @ X26)
% 0.59/0.76          | ~ (v3_funct_2 @ X26 @ X27 @ X28)
% 0.59/0.76          | (v2_funct_2 @ X26 @ X28)
% 0.59/0.76          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.59/0.76      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.59/0.76  thf('30', plain,
% 0.59/0.76      (((v2_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A)
% 0.59/0.76        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)
% 0.59/0.76        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['28', '29'])).
% 0.59/0.76  thf('31', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('32', plain,
% 0.59/0.76      (![X31 : $i, X32 : $i]:
% 0.59/0.76         ((v3_funct_2 @ (k2_funct_2 @ X31 @ X32) @ X31 @ X31)
% 0.59/0.76          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 0.59/0.76          | ~ (v3_funct_2 @ X32 @ X31 @ X31)
% 0.59/0.76          | ~ (v1_funct_2 @ X32 @ X31 @ X31)
% 0.59/0.76          | ~ (v1_funct_1 @ X32))),
% 0.59/0.76      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.59/0.76  thf('33', plain,
% 0.59/0.76      ((~ (v1_funct_1 @ sk_C)
% 0.59/0.76        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.59/0.76        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.59/0.76        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A @ sk_A))),
% 0.59/0.76      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.76  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('35', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('36', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('37', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.59/0.76  thf('38', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)),
% 0.59/0.76      inference('demod', [status(thm)], ['33', '34', '35', '36', '37'])).
% 0.59/0.76  thf('39', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('40', plain,
% 0.59/0.76      (![X31 : $i, X32 : $i]:
% 0.59/0.76         ((v1_funct_1 @ (k2_funct_2 @ X31 @ X32))
% 0.59/0.76          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 0.59/0.76          | ~ (v3_funct_2 @ X32 @ X31 @ X31)
% 0.59/0.76          | ~ (v1_funct_2 @ X32 @ X31 @ X31)
% 0.59/0.76          | ~ (v1_funct_1 @ X32))),
% 0.59/0.76      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.59/0.76  thf('41', plain,
% 0.59/0.76      ((~ (v1_funct_1 @ sk_C)
% 0.59/0.76        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.59/0.76        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.59/0.76        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_C)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['39', '40'])).
% 0.59/0.76  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('43', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('44', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('45', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.59/0.76  thf('46', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.59/0.76  thf('47', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['45', '46'])).
% 0.59/0.76  thf('48', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.59/0.76      inference('demod', [status(thm)], ['30', '38', '47'])).
% 0.59/0.76  thf(d3_funct_2, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.59/0.76       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.59/0.76  thf('49', plain,
% 0.59/0.76      (![X29 : $i, X30 : $i]:
% 0.59/0.76         (~ (v2_funct_2 @ X30 @ X29)
% 0.59/0.76          | ((k2_relat_1 @ X30) = (X29))
% 0.59/0.76          | ~ (v5_relat_1 @ X30 @ X29)
% 0.59/0.76          | ~ (v1_relat_1 @ X30))),
% 0.59/0.76      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.59/0.76  thf('50', plain,
% 0.59/0.76      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.59/0.76        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)
% 0.59/0.76        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['48', '49'])).
% 0.59/0.76  thf('51', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['22', '23'])).
% 0.59/0.76  thf('52', plain,
% 0.59/0.76      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.76      inference('demod', [status(thm)], ['4', '5', '6', '7', '14'])).
% 0.59/0.76  thf('53', plain,
% 0.59/0.76      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.76         ((v5_relat_1 @ X15 @ X17)
% 0.59/0.76          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.59/0.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.59/0.76  thf('54', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.59/0.76      inference('sup-', [status(thm)], ['52', '53'])).
% 0.59/0.76  thf('55', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 0.59/0.76      inference('demod', [status(thm)], ['50', '51', '54'])).
% 0.59/0.76  thf('56', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['22', '23'])).
% 0.59/0.76  thf('57', plain, (((sk_A) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))),
% 0.59/0.76      inference('demod', [status(thm)], ['27', '55', '56'])).
% 0.59/0.76  thf('58', plain,
% 0.59/0.76      ((((sk_A) = (k10_relat_1 @ sk_C @ sk_A))
% 0.59/0.76        | ~ (v1_relat_1 @ sk_C)
% 0.59/0.76        | ~ (v1_funct_1 @ sk_C)
% 0.59/0.76        | ~ (v2_funct_1 @ sk_C))),
% 0.59/0.76      inference('sup+', [status(thm)], ['1', '57'])).
% 0.59/0.76  thf('59', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('60', plain,
% 0.59/0.76      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.76         ((v4_relat_1 @ X15 @ X16)
% 0.59/0.76          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.59/0.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.59/0.76  thf('61', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.59/0.76      inference('sup-', [status(thm)], ['59', '60'])).
% 0.59/0.76  thf('62', plain,
% 0.59/0.76      (![X7 : $i, X8 : $i]:
% 0.59/0.76         (((X7) = (k7_relat_1 @ X7 @ X8))
% 0.59/0.76          | ~ (v4_relat_1 @ X7 @ X8)
% 0.59/0.76          | ~ (v1_relat_1 @ X7))),
% 0.59/0.76      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.59/0.76  thf('63', plain,
% 0.59/0.76      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['61', '62'])).
% 0.59/0.76  thf('64', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('65', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.59/0.76          | (v1_relat_1 @ X0)
% 0.59/0.76          | ~ (v1_relat_1 @ X1))),
% 0.59/0.76      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.59/0.76  thf('66', plain,
% 0.59/0.76      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.59/0.76      inference('sup-', [status(thm)], ['64', '65'])).
% 0.59/0.76  thf('67', plain,
% 0.59/0.76      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.59/0.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.59/0.76  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.76      inference('demod', [status(thm)], ['66', '67'])).
% 0.59/0.76  thf('69', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.59/0.76      inference('demod', [status(thm)], ['63', '68'])).
% 0.59/0.76  thf('70', plain,
% 0.59/0.76      (![X4 : $i, X5 : $i]:
% 0.59/0.76         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.59/0.76          | ~ (v1_relat_1 @ X4))),
% 0.59/0.76      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.59/0.76  thf(t169_relat_1, axiom,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( v1_relat_1 @ A ) =>
% 0.59/0.76       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.59/0.76  thf('71', plain,
% 0.59/0.76      (![X6 : $i]:
% 0.59/0.76         (((k10_relat_1 @ X6 @ (k2_relat_1 @ X6)) = (k1_relat_1 @ X6))
% 0.59/0.76          | ~ (v1_relat_1 @ X6))),
% 0.59/0.76      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.59/0.76  thf('72', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.59/0.76            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.59/0.76          | ~ (v1_relat_1 @ X1)
% 0.59/0.76          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.59/0.76      inference('sup+', [status(thm)], ['70', '71'])).
% 0.59/0.76  thf('73', plain,
% 0.59/0.76      ((~ (v1_relat_1 @ sk_C)
% 0.59/0.76        | ~ (v1_relat_1 @ sk_C)
% 0.59/0.77        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 0.59/0.77            (k9_relat_1 @ sk_C @ sk_A))
% 0.59/0.77            = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['69', '72'])).
% 0.59/0.77  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.77      inference('demod', [status(thm)], ['66', '67'])).
% 0.59/0.77  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.77      inference('demod', [status(thm)], ['66', '67'])).
% 0.59/0.77  thf('76', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['63', '68'])).
% 0.59/0.77  thf('77', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['63', '68'])).
% 0.59/0.77  thf('78', plain,
% 0.59/0.77      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (k1_relat_1 @ sk_C))),
% 0.59/0.77      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 0.59/0.77  thf('79', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['63', '68'])).
% 0.59/0.77  thf('80', plain,
% 0.59/0.77      (![X4 : $i, X5 : $i]:
% 0.59/0.77         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.59/0.77          | ~ (v1_relat_1 @ X4))),
% 0.59/0.77      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.59/0.77  thf('81', plain,
% 0.59/0.77      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.59/0.77        | ~ (v1_relat_1 @ sk_C))),
% 0.59/0.77      inference('sup+', [status(thm)], ['79', '80'])).
% 0.59/0.77  thf('82', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.77      inference('demod', [status(thm)], ['66', '67'])).
% 0.59/0.77  thf('83', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['81', '82'])).
% 0.59/0.77  thf('84', plain,
% 0.59/0.77      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.59/0.77      inference('demod', [status(thm)], ['78', '83'])).
% 0.59/0.77  thf('85', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('86', plain,
% 0.59/0.77      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.59/0.77         (~ (v1_funct_1 @ X26)
% 0.59/0.77          | ~ (v3_funct_2 @ X26 @ X27 @ X28)
% 0.59/0.77          | (v2_funct_2 @ X26 @ X28)
% 0.59/0.77          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.59/0.77      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.59/0.77  thf('87', plain,
% 0.59/0.77      (((v2_funct_2 @ sk_C @ sk_A)
% 0.59/0.77        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.59/0.77        | ~ (v1_funct_1 @ sk_C))),
% 0.59/0.77      inference('sup-', [status(thm)], ['85', '86'])).
% 0.59/0.77  thf('88', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('89', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('90', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.59/0.77  thf('91', plain,
% 0.59/0.77      (![X29 : $i, X30 : $i]:
% 0.59/0.77         (~ (v2_funct_2 @ X30 @ X29)
% 0.59/0.77          | ((k2_relat_1 @ X30) = (X29))
% 0.59/0.77          | ~ (v5_relat_1 @ X30 @ X29)
% 0.59/0.77          | ~ (v1_relat_1 @ X30))),
% 0.59/0.77      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.59/0.77  thf('92', plain,
% 0.59/0.77      ((~ (v1_relat_1 @ sk_C)
% 0.59/0.77        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.59/0.77        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['90', '91'])).
% 0.59/0.77  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.77      inference('demod', [status(thm)], ['66', '67'])).
% 0.59/0.77  thf('94', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('95', plain,
% 0.59/0.77      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.77         ((v5_relat_1 @ X15 @ X17)
% 0.59/0.77          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.59/0.77      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.59/0.77  thf('96', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.59/0.77      inference('sup-', [status(thm)], ['94', '95'])).
% 0.59/0.77  thf('97', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['92', '93', '96'])).
% 0.59/0.77  thf('98', plain, (((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.59/0.77      inference('demod', [status(thm)], ['84', '97'])).
% 0.59/0.77  thf('99', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.77      inference('demod', [status(thm)], ['66', '67'])).
% 0.59/0.77  thf('100', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('101', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('102', plain,
% 0.59/0.77      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.59/0.77         (~ (v1_funct_1 @ X26)
% 0.59/0.77          | ~ (v3_funct_2 @ X26 @ X27 @ X28)
% 0.59/0.77          | (v2_funct_1 @ X26)
% 0.59/0.77          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.59/0.77      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.59/0.77  thf('103', plain,
% 0.59/0.77      (((v2_funct_1 @ sk_C)
% 0.59/0.77        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.59/0.77        | ~ (v1_funct_1 @ sk_C))),
% 0.59/0.77      inference('sup-', [status(thm)], ['101', '102'])).
% 0.59/0.77  thf('104', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('105', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('106', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.77      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.59/0.77  thf('107', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.59/0.77      inference('demod', [status(thm)], ['58', '98', '99', '100', '106'])).
% 0.59/0.77  thf(t164_funct_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.77       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.59/0.77         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.59/0.77  thf('108', plain,
% 0.59/0.77      (![X13 : $i, X14 : $i]:
% 0.59/0.77         (~ (r1_tarski @ X13 @ (k1_relat_1 @ X14))
% 0.59/0.77          | ~ (v2_funct_1 @ X14)
% 0.59/0.77          | ((k10_relat_1 @ X14 @ (k9_relat_1 @ X14 @ X13)) = (X13))
% 0.59/0.77          | ~ (v1_funct_1 @ X14)
% 0.59/0.77          | ~ (v1_relat_1 @ X14))),
% 0.59/0.77      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.59/0.77  thf('109', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (r1_tarski @ X0 @ sk_A)
% 0.59/0.77          | ~ (v1_relat_1 @ sk_C)
% 0.59/0.77          | ~ (v1_funct_1 @ sk_C)
% 0.59/0.77          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0))
% 0.59/0.77          | ~ (v2_funct_1 @ sk_C))),
% 0.59/0.77      inference('sup-', [status(thm)], ['107', '108'])).
% 0.59/0.77  thf('110', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.77      inference('demod', [status(thm)], ['66', '67'])).
% 0.59/0.77  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('112', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.77      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.59/0.77  thf('113', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (r1_tarski @ X0 @ sk_A)
% 0.59/0.77          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.59/0.77      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 0.59/0.77  thf('114', plain,
% 0.59/0.77      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.59/0.77      inference('sup-', [status(thm)], ['0', '113'])).
% 0.59/0.77  thf('115', plain,
% 0.59/0.77      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.59/0.77          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B))
% 0.59/0.77        | ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.59/0.77            (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('116', plain,
% 0.59/0.77      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.59/0.77          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.59/0.77         <= (~
% 0.59/0.77             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.59/0.77                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.59/0.77      inference('split', [status(esa)], ['115'])).
% 0.59/0.77  thf('117', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(redefinition_k7_relset_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.77       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.59/0.77  thf('118', plain,
% 0.59/0.77      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.59/0.77          | ((k7_relset_1 @ X19 @ X20 @ X18 @ X21) = (k9_relat_1 @ X18 @ X21)))),
% 0.59/0.77      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.59/0.77  thf('119', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['117', '118'])).
% 0.59/0.77  thf('120', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(redefinition_k8_relset_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.77       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.59/0.77  thf('121', plain,
% 0.59/0.77      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.59/0.77          | ((k8_relset_1 @ X23 @ X24 @ X22 @ X25) = (k10_relat_1 @ X22 @ X25)))),
% 0.59/0.77      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.59/0.77  thf('122', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['120', '121'])).
% 0.59/0.77  thf('123', plain,
% 0.59/0.77      ((((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B)))
% 0.59/0.77         <= (~
% 0.59/0.77             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.59/0.77                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.59/0.77      inference('demod', [status(thm)], ['116', '119', '122'])).
% 0.59/0.77  thf('124', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('125', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['81', '82'])).
% 0.59/0.77  thf('126', plain,
% 0.59/0.77      (![X4 : $i, X5 : $i]:
% 0.59/0.77         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.59/0.77          | ~ (v1_relat_1 @ X4))),
% 0.59/0.77      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.59/0.77  thf(t147_funct_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.77       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.59/0.77         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.59/0.77  thf('127', plain,
% 0.59/0.77      (![X9 : $i, X10 : $i]:
% 0.59/0.77         (~ (r1_tarski @ X9 @ (k2_relat_1 @ X10))
% 0.59/0.77          | ((k9_relat_1 @ X10 @ (k10_relat_1 @ X10 @ X9)) = (X9))
% 0.59/0.77          | ~ (v1_funct_1 @ X10)
% 0.59/0.77          | ~ (v1_relat_1 @ X10))),
% 0.59/0.77      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.59/0.77  thf('128', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (r1_tarski @ X2 @ (k9_relat_1 @ X1 @ X0))
% 0.59/0.77          | ~ (v1_relat_1 @ X1)
% 0.59/0.77          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.59/0.77          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.59/0.77          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.59/0.77              (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) = (X2)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['126', '127'])).
% 0.59/0.77  thf('129', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (r1_tarski @ X0 @ (k2_relat_1 @ sk_C))
% 0.59/0.77          | ((k9_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 0.59/0.77              (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ X0)) = (X0))
% 0.59/0.77          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ sk_A))
% 0.59/0.77          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))
% 0.59/0.77          | ~ (v1_relat_1 @ sk_C))),
% 0.59/0.77      inference('sup-', [status(thm)], ['125', '128'])).
% 0.59/0.77  thf('130', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['63', '68'])).
% 0.59/0.77  thf('131', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['63', '68'])).
% 0.59/0.77  thf('132', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['63', '68'])).
% 0.59/0.77  thf('133', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('134', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['63', '68'])).
% 0.59/0.77  thf('135', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.77      inference('demod', [status(thm)], ['66', '67'])).
% 0.59/0.77  thf('136', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.77      inference('demod', [status(thm)], ['66', '67'])).
% 0.59/0.77  thf('137', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (r1_tarski @ X0 @ (k2_relat_1 @ sk_C))
% 0.59/0.77          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.59/0.77      inference('demod', [status(thm)],
% 0.59/0.77                ['129', '130', '131', '132', '133', '134', '135', '136'])).
% 0.59/0.77  thf('138', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['92', '93', '96'])).
% 0.59/0.77  thf('139', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (r1_tarski @ X0 @ sk_A)
% 0.59/0.77          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.59/0.77      inference('demod', [status(thm)], ['137', '138'])).
% 0.59/0.77  thf('140', plain,
% 0.59/0.77      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.59/0.77      inference('sup-', [status(thm)], ['124', '139'])).
% 0.59/0.77  thf('141', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['120', '121'])).
% 0.59/0.77  thf('142', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['117', '118'])).
% 0.59/0.77  thf('143', plain,
% 0.59/0.77      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.59/0.77          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.59/0.77         <= (~
% 0.59/0.77             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.59/0.77                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.59/0.77      inference('split', [status(esa)], ['115'])).
% 0.59/0.77  thf('144', plain,
% 0.59/0.77      ((((k9_relat_1 @ sk_C @ (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B))
% 0.59/0.77          != (sk_B)))
% 0.59/0.77         <= (~
% 0.59/0.77             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.59/0.77                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['142', '143'])).
% 0.59/0.77  thf('145', plain,
% 0.59/0.77      ((((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) != (sk_B)))
% 0.59/0.77         <= (~
% 0.59/0.77             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.59/0.77                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['141', '144'])).
% 0.59/0.77  thf('146', plain,
% 0.59/0.77      ((((sk_B) != (sk_B)))
% 0.59/0.77         <= (~
% 0.59/0.77             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.59/0.77                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['140', '145'])).
% 0.59/0.77  thf('147', plain,
% 0.59/0.77      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.59/0.77          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['146'])).
% 0.59/0.77  thf('148', plain,
% 0.59/0.77      (~
% 0.59/0.77       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.59/0.77          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))) | 
% 0.59/0.77       ~
% 0.59/0.77       (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.59/0.77          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.59/0.77      inference('split', [status(esa)], ['115'])).
% 0.59/0.77  thf('149', plain,
% 0.59/0.77      (~
% 0.59/0.77       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.59/0.77          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.59/0.77      inference('sat_resolution*', [status(thm)], ['147', '148'])).
% 0.59/0.77  thf('150', plain,
% 0.59/0.77      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B))),
% 0.59/0.77      inference('simpl_trail', [status(thm)], ['123', '149'])).
% 0.59/0.77  thf('151', plain, ($false),
% 0.59/0.77      inference('simplify_reflect-', [status(thm)], ['114', '150'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

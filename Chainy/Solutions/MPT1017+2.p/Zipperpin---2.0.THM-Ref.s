%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1017+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.alNayAOICe

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:05 EST 2020

% Result     : Theorem 55.10s
% Output     : Refutation 55.10s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 104 expanded)
%              Number of leaves         :   22 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :  403 (1664 expanded)
%              Number of equality atoms :   10 (  46 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_A_16_type,type,(
    sk_A_16: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_99_type,type,(
    sk_B_99: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t83_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ ( B @ ( A @ A ) ) )
        & ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ A ) ) ) ) ) )
     => ( ( ( v2_funct_1 @ B )
          & ( ( k2_relset_1 @ ( A @ ( A @ B ) ) )
            = A ) )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ ( B @ ( A @ A ) ) )
          & ( v3_funct_2 @ ( B @ ( A @ A ) ) )
          & ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ ( B @ ( A @ A ) ) )
          & ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ A ) ) ) ) ) )
       => ( ( ( v2_funct_1 @ B )
            & ( ( k2_relset_1 @ ( A @ ( A @ B ) ) )
              = A ) )
         => ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ ( B @ ( A @ A ) ) )
            & ( v3_funct_2 @ ( B @ ( A @ A ) ) )
            & ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t83_funct_2])).

thf('0',plain,(
    m1_subset_1 @ ( sk_B_99 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_A_16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ ( C @ B ) ) )
       => ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ ( C @ ( A @ B ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X4644: $i,X4645: $i,X4646: $i] :
      ( ~ ( v1_funct_1 @ X4644 )
      | ~ ( v2_funct_1 @ X4644 )
      | ~ ( v2_funct_2 @ ( X4644 @ X4645 ) )
      | ( v3_funct_2 @ ( X4644 @ ( X4646 @ X4645 ) ) )
      | ~ ( m1_subset_1 @ ( X4644 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X4646 @ X4645 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[cc3_funct_2])).

thf('2',plain,
    ( ( v3_funct_2 @ ( sk_B_99 @ ( sk_A_16 @ sk_A_16 ) ) )
    | ~ ( v2_funct_2 @ ( sk_B_99 @ sk_A_16 ) )
    | ~ ( v2_funct_1 @ sk_B_99 )
    | ~ ( v1_funct_1 @ sk_B_99 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_funct_1 @ sk_B_99 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_1 @ sk_B_99 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v3_funct_2 @ ( sk_B_99 @ ( sk_A_16 @ sk_A_16 ) ) )
    | ~ ( v2_funct_2 @ ( sk_B_99 @ sk_A_16 ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_B_99 )
    | ~ ( v1_funct_2 @ ( sk_B_99 @ ( sk_A_16 @ sk_A_16 ) ) )
    | ~ ( v3_funct_2 @ ( sk_B_99 @ ( sk_A_16 @ sk_A_16 ) ) )
    | ~ ( m1_subset_1 @ ( sk_B_99 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_A_16 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( v3_funct_2 @ ( sk_B_99 @ ( sk_A_16 @ sk_A_16 ) ) )
   <= ~ ( v3_funct_2 @ ( sk_B_99 @ ( sk_A_16 @ sk_A_16 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    v1_funct_2 @ ( sk_B_99 @ ( sk_A_16 @ sk_A_16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_funct_2 @ ( sk_B_99 @ ( sk_A_16 @ sk_A_16 ) ) )
   <= ~ ( v1_funct_2 @ ( sk_B_99 @ ( sk_A_16 @ sk_A_16 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('10',plain,(
    v1_funct_2 @ ( sk_B_99 @ ( sk_A_16 @ sk_A_16 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_B_99 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_B_99 )
   <= ~ ( v1_funct_1 @ sk_B_99 ) ),
    inference(split,[status(esa)],['6'])).

thf('13',plain,(
    v1_funct_1 @ sk_B_99 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( sk_B_99 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_A_16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( m1_subset_1 @ ( sk_B_99 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_A_16 ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( sk_B_99 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_A_16 ) ) ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('16',plain,(
    m1_subset_1 @ ( sk_B_99 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_A_16 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v3_funct_2 @ ( sk_B_99 @ ( sk_A_16 @ sk_A_16 ) ) )
    | ~ ( m1_subset_1 @ ( sk_B_99 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_A_16 ) ) ) ) )
    | ~ ( v1_funct_1 @ sk_B_99 )
    | ~ ( v1_funct_2 @ ( sk_B_99 @ ( sk_A_16 @ sk_A_16 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('18',plain,(
    ~ ( v3_funct_2 @ ( sk_B_99 @ ( sk_A_16 @ sk_A_16 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','13','16','17'])).

thf('19',plain,(
    ~ ( v3_funct_2 @ ( sk_B_99 @ ( sk_A_16 @ sk_A_16 ) ) ) ),
    inference(simpl_trail,[status(thm)],['7','18'])).

thf('20',plain,(
    ~ ( v2_funct_2 @ ( sk_B_99 @ sk_A_16 ) ) ),
    inference(clc,[status(thm)],['5','19'])).

thf('21',plain,(
    m1_subset_1 @ ( sk_B_99 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_A_16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( k2_relset_1 @ ( A @ ( B @ C ) ) )
        = ( k2_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X3598: $i,X3599: $i,X3600: $i] :
      ( ( ( k2_relset_1 @ ( X3599 @ ( X3600 @ X3598 ) ) )
        = ( k2_relat_1 @ X3598 ) )
      | ~ ( m1_subset_1 @ ( X3598 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3599 @ X3600 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('23',plain,
    ( ( k2_relset_1 @ ( sk_A_16 @ ( sk_A_16 @ sk_B_99 ) ) )
    = ( k2_relat_1 @ sk_B_99 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_relset_1 @ ( sk_A_16 @ ( sk_A_16 @ sk_B_99 ) ) )
    = sk_A_16 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_relat_1 @ sk_B_99 )
    = sk_A_16 ),
    inference('sup+',[status(thm)],['23','24'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ ( B @ A ) ) )
     => ( ( v2_funct_2 @ ( B @ A ) )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('26',plain,(
    ! [X4669: $i,X4670: $i] :
      ( ( ( k2_relat_1 @ X4670 )
       != X4669 )
      | ( v2_funct_2 @ ( X4670 @ X4669 ) )
      | ~ ( v5_relat_1 @ ( X4670 @ X4669 ) )
      | ~ ( v1_relat_1 @ X4670 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('27',plain,(
    ! [X4670: $i] :
      ( ~ ( v1_relat_1 @ X4670 )
      | ~ ( v5_relat_1 @ ( X4670 @ ( k2_relat_1 @ X4670 ) ) )
      | ( v2_funct_2 @ ( X4670 @ ( k2_relat_1 @ X4670 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ~ ( v5_relat_1 @ ( sk_B_99 @ sk_A_16 ) )
    | ( v2_funct_2 @ ( sk_B_99 @ ( k2_relat_1 @ sk_B_99 ) ) )
    | ~ ( v1_relat_1 @ sk_B_99 ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    m1_subset_1 @ ( sk_B_99 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_A_16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( v4_relat_1 @ ( C @ A ) )
        & ( v5_relat_1 @ ( C @ B ) ) ) ) )).

thf('30',plain,(
    ! [X3536: $i,X3537: $i,X3538: $i] :
      ( ( v5_relat_1 @ ( X3536 @ X3538 ) )
      | ~ ( m1_subset_1 @ ( X3536 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3537 @ X3538 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('31',plain,(
    v5_relat_1 @ ( sk_B_99 @ sk_A_16 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_B_99 )
    = sk_A_16 ),
    inference('sup+',[status(thm)],['23','24'])).

thf('33',plain,(
    m1_subset_1 @ ( sk_B_99 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_A_16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('34',plain,(
    ! [X2039: $i,X2040: $i] :
      ( ~ ( m1_subset_1 @ ( X2039 @ ( k1_zfmisc_1 @ X2040 ) ) )
      | ( v1_relat_1 @ X2039 )
      | ~ ( v1_relat_1 @ X2040 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_A_16 ) ) )
    | ( v1_relat_1 @ sk_B_99 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) )).

thf('36',plain,(
    ! [X2178: $i,X2179: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ ( X2178 @ X2179 ) ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('37',plain,(
    v1_relat_1 @ sk_B_99 ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    v2_funct_2 @ ( sk_B_99 @ sk_A_16 ) ),
    inference(demod,[status(thm)],['28','31','32','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['20','38'])).

%------------------------------------------------------------------------------

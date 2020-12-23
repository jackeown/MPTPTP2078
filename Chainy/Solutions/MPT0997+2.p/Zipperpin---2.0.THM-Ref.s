%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0997+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NLOY2RsLqu

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:04 EST 2020

% Result     : Theorem 38.90s
% Output     : Refutation 38.90s
% Verified   : 
% Statistics : Number of formulae       :   29 (  38 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :  187 ( 387 expanded)
%              Number of equality atoms :   17 (  37 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_16_type,type,(
    sk_A_16: $i )).

thf(sk_C_110_type,type,(
    sk_C_110: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_98_type,type,(
    sk_B_98: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t45_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ ( C @ ( A @ B ) ) )
        & ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k7_relset_1 @ ( A @ ( B @ ( C @ A ) ) ) )
          = ( k2_relset_1 @ ( A @ ( B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ ( C @ ( A @ B ) ) )
          & ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) ) )
       => ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( k7_relset_1 @ ( A @ ( B @ ( C @ A ) ) ) )
            = ( k2_relset_1 @ ( A @ ( B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_funct_2])).

thf('0',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_98 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( ( k7_relset_1 @ ( A @ ( B @ ( C @ A ) ) ) )
          = ( k2_relset_1 @ ( A @ ( B @ C ) ) ) )
        & ( ( k8_relset_1 @ ( A @ ( B @ ( C @ B ) ) ) )
          = ( k1_relset_1 @ ( A @ ( B @ C ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X3707: $i,X3708: $i,X3709: $i] :
      ( ( ( k7_relset_1 @ ( X3707 @ ( X3708 @ ( X3709 @ X3707 ) ) ) )
        = ( k2_relset_1 @ ( X3707 @ ( X3708 @ X3709 ) ) ) )
      | ~ ( m1_subset_1 @ ( X3709 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3707 @ X3708 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('2',plain,
    ( ( k7_relset_1 @ ( sk_A_16 @ ( sk_B_98 @ ( sk_C_110 @ sk_A_16 ) ) ) )
    = ( k2_relset_1 @ ( sk_A_16 @ ( sk_B_98 @ sk_C_110 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_98 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( k2_relset_1 @ ( A @ ( B @ C ) ) )
        = ( k2_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X3598: $i,X3599: $i,X3600: $i] :
      ( ( ( k2_relset_1 @ ( X3599 @ ( X3600 @ X3598 ) ) )
        = ( k2_relat_1 @ X3598 ) )
      | ~ ( m1_subset_1 @ ( X3598 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3599 @ X3600 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('5',plain,
    ( ( k2_relset_1 @ ( sk_A_16 @ ( sk_B_98 @ sk_C_110 ) ) )
    = ( k2_relat_1 @ sk_C_110 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k7_relset_1 @ ( sk_A_16 @ ( sk_B_98 @ ( sk_C_110 @ sk_A_16 ) ) ) )
    = ( k2_relat_1 @ sk_C_110 ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ( k7_relset_1 @ ( sk_A_16 @ ( sk_B_98 @ ( sk_C_110 @ sk_A_16 ) ) ) )
 != ( k2_relset_1 @ ( sk_A_16 @ ( sk_B_98 @ sk_C_110 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k2_relset_1 @ ( sk_A_16 @ ( sk_B_98 @ sk_C_110 ) ) )
    = ( k2_relat_1 @ sk_C_110 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('9',plain,(
    ( k7_relset_1 @ ( sk_A_16 @ ( sk_B_98 @ ( sk_C_110 @ sk_A_16 ) ) ) )
 != ( k2_relat_1 @ sk_C_110 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['6','9'])).

%------------------------------------------------------------------------------

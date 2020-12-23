%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Iev22n9EGD

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:09 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 229 expanded)
%              Number of leaves         :   36 (  83 expanded)
%              Depth                    :   16
%              Number of atoms          :  609 (2394 expanded)
%              Number of equality atoms :   40 ( 111 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X59 ) ) )
      | ( ( k7_relset_1 @ X58 @ X59 @ X57 @ X60 )
        = ( k9_relat_1 @ X57 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X44 @ X45 ) )
        = ( k9_relat_1 @ X44 @ X45 ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('6',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X50 @ X51 ) @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v1_relat_1 @ X47 )
      | ( r1_tarski @ ( k2_relat_1 @ X48 ) @ ( k2_relat_1 @ X47 ) )
      | ~ ( r1_tarski @ X48 @ X47 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X50 @ X51 ) @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X32: $i,X34: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( r1_tarski @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( v1_relat_1 @ X38 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['9','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( v4_relat_1 @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('21',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('22',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v4_relat_1 @ X40 @ X41 )
      | ( r1_tarski @ ( k1_relat_1 @ X40 ) @ X41 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( v1_relat_1 @ X38 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('27',plain,(
    ! [X42: $i,X43: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['23','28'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('30',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X29
        = ( k1_tarski @ X28 ) )
      | ( X29 = k1_xboole_0 )
      | ~ ( r1_tarski @ X29 @ ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('31',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k1_relat_1 @ X53 )
       != ( k1_tarski @ X52 ) )
      | ( ( k2_relat_1 @ X53 )
        = ( k1_tarski @ ( k1_funct_1 @ X53 @ X52 ) ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['33'])).

thf('35',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('37',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('39',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('42',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('43',plain,(
    ! [X49: $i] :
      ( ( ( k1_relat_1 @ X49 )
       != k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('48',plain,(
    ! [X46: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X46 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('49',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('50',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('51',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['4','47','48','49','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Iev22n9EGD
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:13:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.67/0.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.86  % Solved by: fo/fo7.sh
% 0.67/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.86  % done 1437 iterations in 0.408s
% 0.67/0.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.86  % SZS output start Refutation
% 0.67/0.86  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.67/0.86  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.67/0.86  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.67/0.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.86  thf(sk_D_type, type, sk_D: $i).
% 0.67/0.86  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.67/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.86  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.67/0.86  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.67/0.86  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.67/0.86  thf(sk_C_type, type, sk_C: $i).
% 0.67/0.86  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.67/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.86  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.67/0.86  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.67/0.86  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.67/0.86  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.67/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.86  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.67/0.86  thf(t64_funct_2, conjecture,
% 0.67/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.86     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.67/0.86         ( m1_subset_1 @
% 0.67/0.86           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.67/0.86       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.67/0.86         ( r1_tarski @
% 0.67/0.86           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.67/0.86           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.67/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.86    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.86        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.67/0.86            ( m1_subset_1 @
% 0.67/0.86              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.67/0.86          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.67/0.86            ( r1_tarski @
% 0.67/0.86              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.67/0.86              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.67/0.86    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.67/0.86  thf('0', plain,
% 0.67/0.86      (~ (r1_tarski @ 
% 0.67/0.86          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.67/0.86          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('1', plain,
% 0.67/0.86      ((m1_subset_1 @ sk_D @ 
% 0.67/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf(redefinition_k7_relset_1, axiom,
% 0.67/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.86       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.67/0.86  thf('2', plain,
% 0.67/0.86      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 0.67/0.86         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X59)))
% 0.67/0.86          | ((k7_relset_1 @ X58 @ X59 @ X57 @ X60) = (k9_relat_1 @ X57 @ X60)))),
% 0.67/0.86      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.67/0.86  thf('3', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.67/0.86           = (k9_relat_1 @ sk_D @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['1', '2'])).
% 0.67/0.86  thf('4', plain,
% 0.67/0.86      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.67/0.86          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.67/0.86      inference('demod', [status(thm)], ['0', '3'])).
% 0.67/0.86  thf(t148_relat_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( v1_relat_1 @ B ) =>
% 0.67/0.86       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.67/0.86  thf('5', plain,
% 0.67/0.86      (![X44 : $i, X45 : $i]:
% 0.67/0.86         (((k2_relat_1 @ (k7_relat_1 @ X44 @ X45)) = (k9_relat_1 @ X44 @ X45))
% 0.67/0.86          | ~ (v1_relat_1 @ X44))),
% 0.67/0.86      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.67/0.86  thf(t88_relat_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.67/0.86  thf('6', plain,
% 0.67/0.86      (![X50 : $i, X51 : $i]:
% 0.67/0.86         ((r1_tarski @ (k7_relat_1 @ X50 @ X51) @ X50) | ~ (v1_relat_1 @ X50))),
% 0.67/0.86      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.67/0.86  thf(t25_relat_1, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( v1_relat_1 @ A ) =>
% 0.67/0.86       ( ![B:$i]:
% 0.67/0.86         ( ( v1_relat_1 @ B ) =>
% 0.67/0.86           ( ( r1_tarski @ A @ B ) =>
% 0.67/0.86             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.67/0.86               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.67/0.86  thf('7', plain,
% 0.67/0.86      (![X47 : $i, X48 : $i]:
% 0.67/0.86         (~ (v1_relat_1 @ X47)
% 0.67/0.86          | (r1_tarski @ (k2_relat_1 @ X48) @ (k2_relat_1 @ X47))
% 0.67/0.86          | ~ (r1_tarski @ X48 @ X47)
% 0.67/0.86          | ~ (v1_relat_1 @ X48))),
% 0.67/0.86      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.67/0.86  thf('8', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         (~ (v1_relat_1 @ X0)
% 0.67/0.86          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.67/0.86          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.67/0.86             (k2_relat_1 @ X0))
% 0.67/0.86          | ~ (v1_relat_1 @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['6', '7'])).
% 0.67/0.86  thf('9', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.67/0.86           (k2_relat_1 @ X0))
% 0.67/0.86          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.67/0.86          | ~ (v1_relat_1 @ X0))),
% 0.67/0.86      inference('simplify', [status(thm)], ['8'])).
% 0.67/0.86  thf('10', plain,
% 0.67/0.86      (![X50 : $i, X51 : $i]:
% 0.67/0.86         ((r1_tarski @ (k7_relat_1 @ X50 @ X51) @ X50) | ~ (v1_relat_1 @ X50))),
% 0.67/0.86      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.67/0.86  thf(t3_subset, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.67/0.86  thf('11', plain,
% 0.67/0.86      (![X32 : $i, X34 : $i]:
% 0.67/0.86         ((m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X34)) | ~ (r1_tarski @ X32 @ X34))),
% 0.67/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.67/0.86  thf('12', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         (~ (v1_relat_1 @ X0)
% 0.67/0.86          | (m1_subset_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['10', '11'])).
% 0.67/0.86  thf(cc2_relat_1, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( v1_relat_1 @ A ) =>
% 0.67/0.86       ( ![B:$i]:
% 0.67/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.67/0.86  thf('13', plain,
% 0.67/0.86      (![X38 : $i, X39 : $i]:
% 0.67/0.86         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 0.67/0.86          | (v1_relat_1 @ X38)
% 0.67/0.86          | ~ (v1_relat_1 @ X39))),
% 0.67/0.86      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.67/0.86  thf('14', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         (~ (v1_relat_1 @ X0)
% 0.67/0.86          | ~ (v1_relat_1 @ X0)
% 0.67/0.86          | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['12', '13'])).
% 0.67/0.86  thf('15', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 0.67/0.86      inference('simplify', [status(thm)], ['14'])).
% 0.67/0.86  thf('16', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         (~ (v1_relat_1 @ X0)
% 0.67/0.86          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.67/0.86             (k2_relat_1 @ X0)))),
% 0.67/0.86      inference('clc', [status(thm)], ['9', '15'])).
% 0.67/0.86  thf('17', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 0.67/0.86          | ~ (v1_relat_1 @ X1)
% 0.67/0.86          | ~ (v1_relat_1 @ X1))),
% 0.67/0.86      inference('sup+', [status(thm)], ['5', '16'])).
% 0.67/0.86  thf('18', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         (~ (v1_relat_1 @ X1)
% 0.67/0.86          | (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1)))),
% 0.67/0.86      inference('simplify', [status(thm)], ['17'])).
% 0.67/0.86  thf('19', plain,
% 0.67/0.86      ((m1_subset_1 @ sk_D @ 
% 0.67/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf(cc2_relset_1, axiom,
% 0.67/0.86    (![A:$i,B:$i,C:$i]:
% 0.67/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.86       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.67/0.86  thf('20', plain,
% 0.67/0.86      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.67/0.86         ((v4_relat_1 @ X54 @ X55)
% 0.67/0.86          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56))))),
% 0.67/0.86      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.67/0.86  thf('21', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['19', '20'])).
% 0.67/0.86  thf(d18_relat_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( v1_relat_1 @ B ) =>
% 0.67/0.86       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.67/0.86  thf('22', plain,
% 0.67/0.86      (![X40 : $i, X41 : $i]:
% 0.67/0.86         (~ (v4_relat_1 @ X40 @ X41)
% 0.67/0.86          | (r1_tarski @ (k1_relat_1 @ X40) @ X41)
% 0.67/0.86          | ~ (v1_relat_1 @ X40))),
% 0.67/0.86      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.67/0.86  thf('23', plain,
% 0.67/0.86      ((~ (v1_relat_1 @ sk_D)
% 0.67/0.86        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['21', '22'])).
% 0.67/0.86  thf('24', plain,
% 0.67/0.86      ((m1_subset_1 @ sk_D @ 
% 0.67/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('25', plain,
% 0.67/0.86      (![X38 : $i, X39 : $i]:
% 0.67/0.86         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 0.67/0.86          | (v1_relat_1 @ X38)
% 0.67/0.86          | ~ (v1_relat_1 @ X39))),
% 0.67/0.86      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.67/0.86  thf('26', plain,
% 0.67/0.86      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.67/0.86        | (v1_relat_1 @ sk_D))),
% 0.67/0.86      inference('sup-', [status(thm)], ['24', '25'])).
% 0.67/0.86  thf(fc6_relat_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.67/0.86  thf('27', plain,
% 0.67/0.86      (![X42 : $i, X43 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X42 @ X43))),
% 0.67/0.86      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.67/0.86  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 0.67/0.86      inference('demod', [status(thm)], ['26', '27'])).
% 0.67/0.86  thf('29', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['23', '28'])).
% 0.67/0.86  thf(l3_zfmisc_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.67/0.86       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.67/0.86  thf('30', plain,
% 0.67/0.86      (![X28 : $i, X29 : $i]:
% 0.67/0.86         (((X29) = (k1_tarski @ X28))
% 0.67/0.86          | ((X29) = (k1_xboole_0))
% 0.67/0.86          | ~ (r1_tarski @ X29 @ (k1_tarski @ X28)))),
% 0.67/0.86      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.67/0.86  thf('31', plain,
% 0.67/0.86      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.67/0.86        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['29', '30'])).
% 0.67/0.86  thf(t14_funct_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.67/0.86       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.67/0.86         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.67/0.86  thf('32', plain,
% 0.67/0.86      (![X52 : $i, X53 : $i]:
% 0.67/0.86         (((k1_relat_1 @ X53) != (k1_tarski @ X52))
% 0.67/0.86          | ((k2_relat_1 @ X53) = (k1_tarski @ (k1_funct_1 @ X53 @ X52)))
% 0.67/0.86          | ~ (v1_funct_1 @ X53)
% 0.67/0.86          | ~ (v1_relat_1 @ X53))),
% 0.67/0.86      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.67/0.86  thf('33', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.67/0.86          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.67/0.86          | ~ (v1_relat_1 @ X0)
% 0.67/0.86          | ~ (v1_funct_1 @ X0)
% 0.67/0.86          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.67/0.86      inference('sup-', [status(thm)], ['31', '32'])).
% 0.67/0.86  thf('34', plain,
% 0.67/0.86      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.67/0.86        | ~ (v1_funct_1 @ sk_D)
% 0.67/0.86        | ~ (v1_relat_1 @ sk_D)
% 0.67/0.86        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.67/0.86      inference('eq_res', [status(thm)], ['33'])).
% 0.67/0.86  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 0.67/0.86      inference('demod', [status(thm)], ['26', '27'])).
% 0.67/0.86  thf('37', plain,
% 0.67/0.86      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.67/0.86        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.67/0.86      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.67/0.86  thf('38', plain,
% 0.67/0.86      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.67/0.86          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.67/0.86      inference('demod', [status(thm)], ['0', '3'])).
% 0.67/0.86  thf('39', plain,
% 0.67/0.86      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.67/0.86        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['37', '38'])).
% 0.67/0.86  thf('40', plain,
% 0.67/0.86      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['18', '39'])).
% 0.67/0.86  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 0.67/0.86      inference('demod', [status(thm)], ['26', '27'])).
% 0.67/0.86  thf('42', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.67/0.86      inference('demod', [status(thm)], ['40', '41'])).
% 0.67/0.86  thf(t64_relat_1, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( v1_relat_1 @ A ) =>
% 0.67/0.86       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.67/0.86           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.67/0.86         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.67/0.86  thf('43', plain,
% 0.67/0.86      (![X49 : $i]:
% 0.67/0.86         (((k1_relat_1 @ X49) != (k1_xboole_0))
% 0.67/0.86          | ((X49) = (k1_xboole_0))
% 0.67/0.86          | ~ (v1_relat_1 @ X49))),
% 0.67/0.86      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.67/0.86  thf('44', plain,
% 0.67/0.86      ((((k1_xboole_0) != (k1_xboole_0))
% 0.67/0.86        | ~ (v1_relat_1 @ sk_D)
% 0.67/0.86        | ((sk_D) = (k1_xboole_0)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['42', '43'])).
% 0.67/0.86  thf('45', plain, ((v1_relat_1 @ sk_D)),
% 0.67/0.86      inference('demod', [status(thm)], ['26', '27'])).
% 0.67/0.86  thf('46', plain,
% 0.67/0.86      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.67/0.86      inference('demod', [status(thm)], ['44', '45'])).
% 0.67/0.86  thf('47', plain, (((sk_D) = (k1_xboole_0))),
% 0.67/0.86      inference('simplify', [status(thm)], ['46'])).
% 0.67/0.86  thf(t150_relat_1, axiom,
% 0.67/0.86    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.67/0.86  thf('48', plain,
% 0.67/0.86      (![X46 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X46) = (k1_xboole_0))),
% 0.67/0.86      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.67/0.86  thf('49', plain, (((sk_D) = (k1_xboole_0))),
% 0.67/0.86      inference('simplify', [status(thm)], ['46'])).
% 0.67/0.86  thf(t4_subset_1, axiom,
% 0.67/0.86    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.67/0.86  thf('50', plain,
% 0.67/0.86      (![X31 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 0.67/0.86      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.67/0.86  thf('51', plain,
% 0.67/0.86      (![X32 : $i, X33 : $i]:
% 0.67/0.86         ((r1_tarski @ X32 @ X33) | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 0.67/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.67/0.86  thf('52', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.67/0.86      inference('sup-', [status(thm)], ['50', '51'])).
% 0.67/0.86  thf('53', plain, ($false),
% 0.67/0.86      inference('demod', [status(thm)], ['4', '47', '48', '49', '52'])).
% 0.67/0.86  
% 0.67/0.86  % SZS output end Refutation
% 0.67/0.86  
% 0.67/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

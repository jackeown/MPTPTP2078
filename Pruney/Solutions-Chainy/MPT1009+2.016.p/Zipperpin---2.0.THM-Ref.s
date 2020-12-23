%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aze9jaN51O

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:50 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  147 (1658 expanded)
%              Number of leaves         :   34 ( 501 expanded)
%              Depth                    :   19
%              Number of atoms          : 1011 (14243 expanded)
%              Number of equality atoms :  115 (1180 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k7_relset_1 @ X35 @ X36 @ X34 @ X37 )
        = ( k9_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X22 @ X23 ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X9 ) )
      | ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('16',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k1_relat_1 @ X27 )
       != ( k1_tarski @ X26 ) )
      | ( ( k2_relat_1 @ X27 )
        = ( k1_tarski @ ( k1_funct_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('22',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('24',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('27',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('28',plain,(
    ! [X24: $i] :
      ( ( ( k1_relat_1 @ X24 )
       != k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('29',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('34',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['35'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('37',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['34','40'])).

thf('42',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('45',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('46',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('47',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['43','47'])).

thf('49',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('52',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('56',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('57',plain,(
    v1_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['43','47'])).

thf('60',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k1_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) )
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('63',plain,(
    ! [X25: $i] :
      ( ( ( k1_relat_1 @ X25 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X25 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('64',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( ( k2_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('66',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k1_relat_1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['43','47'])).

thf('68',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X9 ) )
      | ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('71',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('72',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_D ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['43','47'])).

thf('75',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['76'])).

thf('78',plain,
    ( ( ( k1_relat_1 @ sk_D )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('81',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['43','47'])).

thf('82',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('83',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X9 ) )
      | ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ ( k1_tarski @ X11 ) )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('87',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X11 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['43','47'])).

thf('92',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','92'])).

thf('94',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['79','94'])).

thf('96',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['79','94'])).

thf('97',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','95','96'])).

thf('98',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X22 @ X23 ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('100',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['43','47'])).

thf('104',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['79','94'])).

thf('105',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['97'])).

thf('107',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['45','46'])).

thf('108',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['102','105','106','107'])).

thf('109',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('110',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('111',plain,(
    $false ),
    inference(demod,[status(thm)],['4','32','108','109','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aze9jaN51O
% 0.15/0.36  % Computer   : n014.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 12:55:07 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 327 iterations in 0.131s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.43/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.61  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.43/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.43/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.43/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.61  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.43/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.43/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.43/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.43/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.43/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.43/0.61  thf(t64_funct_2, conjecture,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.43/0.61         ( m1_subset_1 @
% 0.43/0.61           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.43/0.61       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.43/0.61         ( r1_tarski @
% 0.43/0.61           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.43/0.61           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.61        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.43/0.61            ( m1_subset_1 @
% 0.43/0.61              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.43/0.61          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.43/0.61            ( r1_tarski @
% 0.43/0.61              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.43/0.61              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.43/0.61  thf('0', plain,
% 0.43/0.61      (~ (r1_tarski @ 
% 0.43/0.61          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.43/0.61          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_D @ 
% 0.43/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(redefinition_k7_relset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.61       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.43/0.61          | ((k7_relset_1 @ X35 @ X36 @ X34 @ X37) = (k9_relat_1 @ X34 @ X37)))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.43/0.61  thf('3', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.43/0.61           = (k9_relat_1 @ sk_D @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.43/0.61  thf('4', plain,
% 0.43/0.61      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.43/0.61          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['0', '3'])).
% 0.43/0.61  thf(t144_relat_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ B ) =>
% 0.43/0.61       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.43/0.61  thf('5', plain,
% 0.43/0.61      (![X22 : $i, X23 : $i]:
% 0.43/0.61         ((r1_tarski @ (k9_relat_1 @ X22 @ X23) @ (k2_relat_1 @ X22))
% 0.43/0.61          | ~ (v1_relat_1 @ X22))),
% 0.43/0.61      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.43/0.61  thf('6', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_D @ 
% 0.43/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(cc2_relset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.43/0.61  thf('7', plain,
% 0.43/0.61      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.43/0.61         ((v4_relat_1 @ X31 @ X32)
% 0.43/0.61          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.43/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.43/0.61  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.43/0.61  thf(d18_relat_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ B ) =>
% 0.43/0.61       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.43/0.61  thf('9', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i]:
% 0.43/0.61         (~ (v4_relat_1 @ X18 @ X19)
% 0.43/0.61          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 0.43/0.61          | ~ (v1_relat_1 @ X18))),
% 0.43/0.61      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.43/0.61  thf('10', plain,
% 0.43/0.61      ((~ (v1_relat_1 @ sk_D)
% 0.43/0.61        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.43/0.61  thf('11', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_D @ 
% 0.43/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(cc1_relset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.61       ( v1_relat_1 @ C ) ))).
% 0.43/0.61  thf('12', plain,
% 0.43/0.61      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.43/0.61         ((v1_relat_1 @ X28)
% 0.43/0.61          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.43/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.43/0.61  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 0.43/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.43/0.61  thf('14', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['10', '13'])).
% 0.43/0.61  thf(l3_zfmisc_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.43/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.43/0.61  thf('15', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i]:
% 0.43/0.61         (((X10) = (k1_tarski @ X9))
% 0.43/0.61          | ((X10) = (k1_xboole_0))
% 0.43/0.61          | ~ (r1_tarski @ X10 @ (k1_tarski @ X9)))),
% 0.43/0.61      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.43/0.61  thf('16', plain,
% 0.43/0.61      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.43/0.61        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.43/0.61  thf(t14_funct_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.43/0.61       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.43/0.61         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.43/0.61  thf('17', plain,
% 0.43/0.61      (![X26 : $i, X27 : $i]:
% 0.43/0.61         (((k1_relat_1 @ X27) != (k1_tarski @ X26))
% 0.43/0.61          | ((k2_relat_1 @ X27) = (k1_tarski @ (k1_funct_1 @ X27 @ X26)))
% 0.43/0.61          | ~ (v1_funct_1 @ X27)
% 0.43/0.61          | ~ (v1_relat_1 @ X27))),
% 0.43/0.61      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.43/0.61  thf('18', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.43/0.61          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.43/0.61          | ~ (v1_relat_1 @ X0)
% 0.43/0.61          | ~ (v1_funct_1 @ X0)
% 0.43/0.61          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.43/0.61  thf('19', plain,
% 0.43/0.61      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.43/0.61        | ~ (v1_funct_1 @ sk_D)
% 0.43/0.61        | ~ (v1_relat_1 @ sk_D)
% 0.43/0.61        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.43/0.61      inference('eq_res', [status(thm)], ['18'])).
% 0.43/0.61  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 0.43/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.43/0.61  thf('22', plain,
% 0.43/0.61      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.43/0.61        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.43/0.61      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.43/0.61  thf('23', plain,
% 0.43/0.61      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.43/0.61          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['0', '3'])).
% 0.43/0.61  thf('24', plain,
% 0.43/0.61      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.43/0.61        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.43/0.61  thf('25', plain,
% 0.43/0.61      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['5', '24'])).
% 0.43/0.61  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.43/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.43/0.61  thf('27', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['25', '26'])).
% 0.43/0.61  thf(t64_relat_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ A ) =>
% 0.43/0.61       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.43/0.61           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.43/0.61         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.43/0.61  thf('28', plain,
% 0.43/0.61      (![X24 : $i]:
% 0.43/0.61         (((k1_relat_1 @ X24) != (k1_xboole_0))
% 0.43/0.61          | ((X24) = (k1_xboole_0))
% 0.43/0.61          | ~ (v1_relat_1 @ X24))),
% 0.43/0.61      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.43/0.61  thf('29', plain,
% 0.43/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.43/0.61        | ~ (v1_relat_1 @ sk_D)
% 0.43/0.61        | ((sk_D) = (k1_xboole_0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.43/0.61  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 0.43/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.43/0.61  thf('31', plain,
% 0.43/0.61      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.43/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.43/0.61  thf('32', plain, (((sk_D) = (k1_xboole_0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['31'])).
% 0.43/0.61  thf(t113_zfmisc_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.43/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.43/0.61  thf('33', plain,
% 0.43/0.61      (![X13 : $i, X14 : $i]:
% 0.43/0.61         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.43/0.61          | ((X14) != (k1_xboole_0)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.43/0.61  thf('34', plain,
% 0.43/0.61      (![X13 : $i]: ((k2_zfmisc_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['33'])).
% 0.43/0.61  thf(d10_xboole_0, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.43/0.61  thf('35', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.43/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.61  thf('36', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.43/0.61      inference('simplify', [status(thm)], ['35'])).
% 0.43/0.61  thf(t3_subset, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.43/0.61  thf('37', plain,
% 0.43/0.61      (![X15 : $i, X17 : $i]:
% 0.43/0.61         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.43/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.43/0.61  thf('38', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['36', '37'])).
% 0.43/0.61  thf('39', plain,
% 0.43/0.61      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.43/0.61         ((v4_relat_1 @ X31 @ X32)
% 0.43/0.61          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.43/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.43/0.61  thf('40', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 0.43/0.61      inference('sup-', [status(thm)], ['38', '39'])).
% 0.43/0.61  thf('41', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 0.43/0.61      inference('sup+', [status(thm)], ['34', '40'])).
% 0.43/0.61  thf('42', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i]:
% 0.43/0.61         (~ (v4_relat_1 @ X18 @ X19)
% 0.43/0.61          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 0.43/0.61          | ~ (v1_relat_1 @ X18))),
% 0.43/0.61      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.43/0.61  thf('43', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ k1_xboole_0)
% 0.43/0.61          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['41', '42'])).
% 0.43/0.61  thf('44', plain,
% 0.43/0.61      (![X13 : $i, X14 : $i]:
% 0.43/0.61         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.43/0.61          | ((X13) != (k1_xboole_0)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.43/0.61  thf('45', plain,
% 0.43/0.61      (![X14 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['44'])).
% 0.43/0.61  thf(fc6_relat_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.43/0.61  thf('46', plain,
% 0.43/0.61      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 0.43/0.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.43/0.61  thf('47', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.43/0.61      inference('sup+', [status(thm)], ['45', '46'])).
% 0.43/0.61  thf('48', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.43/0.61      inference('demod', [status(thm)], ['43', '47'])).
% 0.43/0.61  thf('49', plain,
% 0.43/0.61      (![X15 : $i, X17 : $i]:
% 0.43/0.61         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.43/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.43/0.61  thf('50', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (m1_subset_1 @ (k1_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['48', '49'])).
% 0.43/0.61  thf('51', plain,
% 0.43/0.61      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.43/0.61         ((v4_relat_1 @ X31 @ X32)
% 0.43/0.61          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.43/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.43/0.61  thf('52', plain,
% 0.43/0.61      (![X1 : $i]: (v4_relat_1 @ (k1_relat_1 @ k1_xboole_0) @ X1)),
% 0.43/0.61      inference('sup-', [status(thm)], ['50', '51'])).
% 0.43/0.61  thf('53', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i]:
% 0.43/0.61         (~ (v4_relat_1 @ X18 @ X19)
% 0.43/0.61          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 0.43/0.61          | ~ (v1_relat_1 @ X18))),
% 0.43/0.61      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.43/0.61  thf('54', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ (k1_relat_1 @ k1_xboole_0))
% 0.43/0.61          | (r1_tarski @ (k1_relat_1 @ (k1_relat_1 @ k1_xboole_0)) @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['52', '53'])).
% 0.43/0.61  thf('55', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (m1_subset_1 @ (k1_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['48', '49'])).
% 0.43/0.61  thf('56', plain,
% 0.43/0.61      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.43/0.61         ((v1_relat_1 @ X28)
% 0.43/0.61          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.43/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.43/0.61  thf('57', plain, ((v1_relat_1 @ (k1_relat_1 @ k1_xboole_0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['55', '56'])).
% 0.43/0.61  thf('58', plain,
% 0.43/0.61      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k1_relat_1 @ k1_xboole_0)) @ X0)),
% 0.43/0.61      inference('demod', [status(thm)], ['54', '57'])).
% 0.43/0.61  thf('59', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.43/0.61      inference('demod', [status(thm)], ['43', '47'])).
% 0.43/0.61  thf('60', plain,
% 0.43/0.61      (![X0 : $i, X2 : $i]:
% 0.43/0.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.43/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.61  thf('61', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (r1_tarski @ X0 @ (k1_relat_1 @ k1_xboole_0))
% 0.43/0.61          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['59', '60'])).
% 0.43/0.61  thf('62', plain,
% 0.43/0.61      (((k1_relat_1 @ (k1_relat_1 @ k1_xboole_0)) = (k1_relat_1 @ k1_xboole_0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['58', '61'])).
% 0.43/0.61  thf(t65_relat_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ A ) =>
% 0.43/0.61       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.43/0.61         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.43/0.61  thf('63', plain,
% 0.43/0.61      (![X25 : $i]:
% 0.43/0.61         (((k1_relat_1 @ X25) != (k1_xboole_0))
% 0.43/0.61          | ((k2_relat_1 @ X25) = (k1_xboole_0))
% 0.43/0.61          | ~ (v1_relat_1 @ X25))),
% 0.43/0.61      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.43/0.61  thf('64', plain,
% 0.43/0.61      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.43/0.61        | ~ (v1_relat_1 @ (k1_relat_1 @ k1_xboole_0))
% 0.43/0.61        | ((k2_relat_1 @ (k1_relat_1 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.43/0.61  thf('65', plain, ((v1_relat_1 @ (k1_relat_1 @ k1_xboole_0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['55', '56'])).
% 0.43/0.61  thf('66', plain,
% 0.43/0.61      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.43/0.61        | ((k2_relat_1 @ (k1_relat_1 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.43/0.61      inference('demod', [status(thm)], ['64', '65'])).
% 0.43/0.61  thf('67', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.43/0.61      inference('demod', [status(thm)], ['43', '47'])).
% 0.43/0.61  thf('68', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i]:
% 0.43/0.61         (((X10) = (k1_tarski @ X9))
% 0.43/0.61          | ((X10) = (k1_xboole_0))
% 0.43/0.61          | ~ (r1_tarski @ X10 @ (k1_tarski @ X9)))),
% 0.43/0.61      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.43/0.61  thf('69', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.43/0.61          | ((k1_relat_1 @ k1_xboole_0) = (k1_tarski @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['67', '68'])).
% 0.43/0.61  thf('70', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['10', '13'])).
% 0.43/0.61  thf('71', plain,
% 0.43/0.61      (![X0 : $i, X2 : $i]:
% 0.43/0.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.43/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.61  thf('72', plain,
% 0.43/0.61      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_D))
% 0.43/0.61        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['70', '71'])).
% 0.43/0.61  thf('73', plain,
% 0.43/0.61      ((~ (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ (k1_relat_1 @ sk_D))
% 0.43/0.61        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.43/0.61        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['69', '72'])).
% 0.43/0.61  thf('74', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.43/0.61      inference('demod', [status(thm)], ['43', '47'])).
% 0.43/0.61  thf('75', plain,
% 0.43/0.61      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.43/0.61        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D)))),
% 0.43/0.61      inference('demod', [status(thm)], ['73', '74'])).
% 0.43/0.61  thf('76', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.43/0.61          | ((k1_relat_1 @ k1_xboole_0) = (k1_tarski @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['67', '68'])).
% 0.43/0.61  thf('77', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k1_tarski @ X0) != (k1_xboole_0))
% 0.43/0.61          | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.43/0.61      inference('eq_fact', [status(thm)], ['76'])).
% 0.43/0.61  thf('78', plain,
% 0.43/0.61      ((((k1_relat_1 @ sk_D) != (k1_xboole_0))
% 0.43/0.61        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.43/0.61        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['75', '77'])).
% 0.43/0.61  thf('79', plain,
% 0.43/0.61      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.43/0.61        | ((k1_relat_1 @ sk_D) != (k1_xboole_0)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['78'])).
% 0.43/0.61  thf('80', plain,
% 0.43/0.61      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.43/0.61        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.43/0.61  thf('81', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.43/0.61      inference('demod', [status(thm)], ['43', '47'])).
% 0.43/0.61  thf('82', plain,
% 0.43/0.61      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.43/0.61        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.43/0.61  thf('83', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i]:
% 0.43/0.61         (((X10) = (k1_tarski @ X9))
% 0.43/0.61          | ((X10) = (k1_xboole_0))
% 0.43/0.61          | ~ (r1_tarski @ X10 @ (k1_tarski @ X9)))),
% 0.43/0.61      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.43/0.61  thf('84', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_D))
% 0.43/0.61          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.43/0.61          | ((X0) = (k1_xboole_0))
% 0.43/0.61          | ((X0) = (k1_tarski @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['82', '83'])).
% 0.43/0.61  thf('85', plain,
% 0.43/0.61      ((((k1_relat_1 @ k1_xboole_0) = (k1_tarski @ sk_A))
% 0.43/0.61        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.43/0.61        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['81', '84'])).
% 0.43/0.61  thf('86', plain,
% 0.43/0.61      (![X10 : $i, X11 : $i]:
% 0.43/0.61         ((r1_tarski @ X10 @ (k1_tarski @ X11)) | ((X10) != (k1_xboole_0)))),
% 0.43/0.61      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.43/0.61  thf('87', plain,
% 0.43/0.61      (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X11))),
% 0.43/0.61      inference('simplify', [status(thm)], ['86'])).
% 0.43/0.61  thf('88', plain,
% 0.43/0.61      (![X0 : $i, X2 : $i]:
% 0.43/0.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.43/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.61  thf('89', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (r1_tarski @ (k1_tarski @ X0) @ k1_xboole_0)
% 0.43/0.61          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['87', '88'])).
% 0.43/0.61  thf('90', plain,
% 0.43/0.61      ((~ (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)
% 0.43/0.61        | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.43/0.61        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.43/0.61        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['85', '89'])).
% 0.43/0.61  thf('91', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.43/0.61      inference('demod', [status(thm)], ['43', '47'])).
% 0.43/0.61  thf('92', plain,
% 0.43/0.61      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.43/0.61        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.43/0.61        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.43/0.61      inference('demod', [status(thm)], ['90', '91'])).
% 0.43/0.61  thf('93', plain,
% 0.43/0.61      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.43/0.61        | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.43/0.61        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.43/0.61        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['80', '92'])).
% 0.43/0.61  thf('94', plain,
% 0.43/0.61      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.43/0.61        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['93'])).
% 0.43/0.61  thf('95', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.61      inference('clc', [status(thm)], ['79', '94'])).
% 0.43/0.61  thf('96', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.61      inference('clc', [status(thm)], ['79', '94'])).
% 0.43/0.61  thf('97', plain,
% 0.43/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.43/0.61        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.43/0.61      inference('demod', [status(thm)], ['66', '95', '96'])).
% 0.43/0.61  thf('98', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['97'])).
% 0.43/0.61  thf('99', plain,
% 0.43/0.61      (![X22 : $i, X23 : $i]:
% 0.43/0.61         ((r1_tarski @ (k9_relat_1 @ X22 @ X23) @ (k2_relat_1 @ X22))
% 0.43/0.61          | ~ (v1_relat_1 @ X22))),
% 0.43/0.61      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.43/0.61  thf('100', plain,
% 0.43/0.61      (![X0 : $i, X2 : $i]:
% 0.43/0.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.43/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.61  thf('101', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (v1_relat_1 @ X0)
% 0.43/0.61          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k9_relat_1 @ X0 @ X1))
% 0.43/0.61          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['99', '100'])).
% 0.43/0.61  thf('102', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (r1_tarski @ k1_xboole_0 @ (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.43/0.61          | ((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.43/0.61          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['98', '101'])).
% 0.43/0.61  thf('103', plain,
% 0.43/0.61      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.43/0.61      inference('demod', [status(thm)], ['43', '47'])).
% 0.43/0.61  thf('104', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.61      inference('clc', [status(thm)], ['79', '94'])).
% 0.43/0.61  thf('105', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.43/0.61      inference('demod', [status(thm)], ['103', '104'])).
% 0.43/0.61  thf('106', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['97'])).
% 0.43/0.61  thf('107', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.43/0.61      inference('sup+', [status(thm)], ['45', '46'])).
% 0.43/0.61  thf('108', plain,
% 0.43/0.61      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.43/0.61      inference('demod', [status(thm)], ['102', '105', '106', '107'])).
% 0.43/0.61  thf('109', plain, (((sk_D) = (k1_xboole_0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['31'])).
% 0.43/0.61  thf('110', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.43/0.61      inference('demod', [status(thm)], ['103', '104'])).
% 0.43/0.61  thf('111', plain, ($false),
% 0.43/0.61      inference('demod', [status(thm)], ['4', '32', '108', '109', '110'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.46/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

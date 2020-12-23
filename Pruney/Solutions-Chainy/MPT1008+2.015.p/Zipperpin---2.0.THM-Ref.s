%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0rIYTUrjpv

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:33 EST 2020

% Result     : Theorem 2.80s
% Output     : Refutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 430 expanded)
%              Number of leaves         :   44 ( 145 expanded)
%              Depth                    :   17
%              Number of atoms          :  895 (5291 expanded)
%              Number of equality atoms :   88 ( 434 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('0',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( v1_funct_2 @ X56 @ X54 @ X55 )
      | ( X54
        = ( k1_relset_1 @ X54 @ X55 @ X56 ) )
      | ~ ( zip_tseitin_1 @ X56 @ X55 @ X54 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X52: $i,X53: $i] :
      ( ( zip_tseitin_0 @ X52 @ X53 )
      | ( X52 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ~ ( zip_tseitin_0 @ X57 @ X58 )
      | ( zip_tseitin_1 @ X59 @ X57 @ X58 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v4_relat_1 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    v4_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v4_relat_1 @ X27 @ X28 )
      | ( r1_tarski @ ( k1_relat_1 @ X27 ) @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('17',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_relat_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('18',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15
        = ( k1_tarski @ X14 ) )
      | ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('21',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k1_relat_1 @ X31 )
       != ( k1_tarski @ X30 ) )
      | ( ( k2_relat_1 @ X31 )
        = ( k1_tarski @ ( k1_funct_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C_1 ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['23'])).

thf('25',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('27',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( ( k2_relset_1 @ X43 @ X44 @ X42 )
        = ( k2_relat_1 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('31',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['27','32'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('34',plain,(
    ! [X29: $i] :
      ( ( ( k1_relat_1 @ X29 )
       != k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('39',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t39_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
          = ( k2_relset_1 @ B @ A @ C ) )
        & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
          = ( k1_relset_1 @ B @ A @ C ) ) ) ) )).

thf('40',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( ( k8_relset_1 @ X49 @ X50 @ X51 @ ( k7_relset_1 @ X49 @ X50 @ X51 @ X49 ) )
        = ( k1_relset_1 @ X49 @ X50 @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[t39_relset_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X1 ) )
      = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('43',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k8_relset_1 @ X46 @ X47 @ X45 @ X48 )
        = ( k10_relat_1 @ X45 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X1 ) )
      = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X39 @ X40 @ X38 @ X41 ) @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('50',plain,(
    ! [X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ k1_xboole_0 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('51',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('54',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('56',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','58'])).

thf('60',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','38','59'])).

thf('61',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['27','32'])).

thf('62',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k1_relat_1 @ X31 )
       != ( k1_tarski @ X30 ) )
      | ( ( k2_relat_1 @ X31 )
        = ( k1_tarski @ ( k1_funct_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( ( k2_relat_1 @ sk_C_1 )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('65',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_C_1 )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('68',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('73',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('74',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('75',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['71','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0rIYTUrjpv
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:40:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.80/2.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.80/2.99  % Solved by: fo/fo7.sh
% 2.80/2.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.80/2.99  % done 2662 iterations in 2.501s
% 2.80/2.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.80/2.99  % SZS output start Refutation
% 2.80/2.99  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.80/2.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.80/2.99  thf(sk_B_type, type, sk_B: $i).
% 2.80/2.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.80/2.99  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.80/2.99  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.80/2.99  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.80/2.99  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.80/2.99  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.80/2.99  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.80/2.99  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 2.80/2.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.80/2.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.80/2.99  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.80/2.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.80/2.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.80/2.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.80/2.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.80/2.99  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.80/2.99  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 2.80/2.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.80/2.99  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.80/2.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.80/2.99  thf(sk_A_type, type, sk_A: $i).
% 2.80/2.99  thf(t62_funct_2, conjecture,
% 2.80/2.99    (![A:$i,B:$i,C:$i]:
% 2.80/2.99     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 2.80/2.99         ( m1_subset_1 @
% 2.80/2.99           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 2.80/2.99       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 2.80/2.99         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 2.80/2.99           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 2.80/2.99  thf(zf_stmt_0, negated_conjecture,
% 2.80/2.99    (~( ![A:$i,B:$i,C:$i]:
% 2.80/2.99        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 2.80/2.99            ( m1_subset_1 @
% 2.80/2.99              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 2.80/2.99          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 2.80/2.99            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 2.80/2.99              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 2.80/2.99    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 2.80/2.99  thf('0', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 2.80/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.80/2.99  thf(d1_funct_2, axiom,
% 2.80/2.99    (![A:$i,B:$i,C:$i]:
% 2.80/2.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.80/2.99       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.80/2.99           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.80/2.99             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.80/2.99         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.80/2.99           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.80/2.99             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.80/2.99  thf(zf_stmt_1, axiom,
% 2.80/2.99    (![C:$i,B:$i,A:$i]:
% 2.80/2.99     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.80/2.99       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.80/2.99  thf('1', plain,
% 2.80/2.99      (![X54 : $i, X55 : $i, X56 : $i]:
% 2.80/2.99         (~ (v1_funct_2 @ X56 @ X54 @ X55)
% 2.80/2.99          | ((X54) = (k1_relset_1 @ X54 @ X55 @ X56))
% 2.80/2.99          | ~ (zip_tseitin_1 @ X56 @ X55 @ X54))),
% 2.80/2.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.80/2.99  thf('2', plain,
% 2.80/2.99      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))
% 2.80/2.99        | ((k1_tarski @ sk_A)
% 2.80/2.99            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)))),
% 2.80/2.99      inference('sup-', [status(thm)], ['0', '1'])).
% 2.80/2.99  thf(zf_stmt_2, axiom,
% 2.80/2.99    (![B:$i,A:$i]:
% 2.80/2.99     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.80/2.99       ( zip_tseitin_0 @ B @ A ) ))).
% 2.80/2.99  thf('3', plain,
% 2.80/2.99      (![X52 : $i, X53 : $i]:
% 2.80/2.99         ((zip_tseitin_0 @ X52 @ X53) | ((X52) = (k1_xboole_0)))),
% 2.80/2.99      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.80/2.99  thf('4', plain,
% 2.80/2.99      ((m1_subset_1 @ sk_C_1 @ 
% 2.80/2.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 2.80/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.80/2.99  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.80/2.99  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.80/2.99  thf(zf_stmt_5, axiom,
% 2.80/2.99    (![A:$i,B:$i,C:$i]:
% 2.80/2.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.80/2.99       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.80/2.99         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.80/2.99           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.80/2.99             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.80/2.99  thf('5', plain,
% 2.80/2.99      (![X57 : $i, X58 : $i, X59 : $i]:
% 2.80/2.99         (~ (zip_tseitin_0 @ X57 @ X58)
% 2.80/2.99          | (zip_tseitin_1 @ X59 @ X57 @ X58)
% 2.80/2.99          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X57))))),
% 2.80/2.99      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.80/2.99  thf('6', plain,
% 2.80/2.99      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))
% 2.80/2.99        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 2.80/2.99      inference('sup-', [status(thm)], ['4', '5'])).
% 2.80/2.99  thf('7', plain,
% 2.80/2.99      ((((sk_B) = (k1_xboole_0))
% 2.80/2.99        | (zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 2.80/2.99      inference('sup-', [status(thm)], ['3', '6'])).
% 2.80/2.99  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 2.80/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.80/2.99  thf('9', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))),
% 2.80/2.99      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 2.80/2.99  thf('10', plain,
% 2.80/2.99      (((k1_tarski @ sk_A) = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1))),
% 2.80/2.99      inference('demod', [status(thm)], ['2', '9'])).
% 2.80/2.99  thf('11', plain,
% 2.80/2.99      ((m1_subset_1 @ sk_C_1 @ 
% 2.80/2.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 2.80/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.80/2.99  thf(cc2_relset_1, axiom,
% 2.80/2.99    (![A:$i,B:$i,C:$i]:
% 2.80/2.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.80/2.99       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.80/2.99  thf('12', plain,
% 2.80/2.99      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.80/2.99         ((v4_relat_1 @ X35 @ X36)
% 2.80/2.99          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 2.80/2.99      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.80/2.99  thf('13', plain, ((v4_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))),
% 2.80/2.99      inference('sup-', [status(thm)], ['11', '12'])).
% 2.80/2.99  thf(d18_relat_1, axiom,
% 2.80/2.99    (![A:$i,B:$i]:
% 2.80/2.99     ( ( v1_relat_1 @ B ) =>
% 2.80/2.99       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.80/2.99  thf('14', plain,
% 2.80/2.99      (![X27 : $i, X28 : $i]:
% 2.80/2.99         (~ (v4_relat_1 @ X27 @ X28)
% 2.80/2.99          | (r1_tarski @ (k1_relat_1 @ X27) @ X28)
% 2.80/2.99          | ~ (v1_relat_1 @ X27))),
% 2.80/2.99      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.80/2.99  thf('15', plain,
% 2.80/2.99      ((~ (v1_relat_1 @ sk_C_1)
% 2.80/2.99        | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_tarski @ sk_A)))),
% 2.80/2.99      inference('sup-', [status(thm)], ['13', '14'])).
% 2.80/2.99  thf('16', plain,
% 2.80/2.99      ((m1_subset_1 @ sk_C_1 @ 
% 2.80/2.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 2.80/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.80/2.99  thf(cc1_relset_1, axiom,
% 2.80/2.99    (![A:$i,B:$i,C:$i]:
% 2.80/2.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.80/2.99       ( v1_relat_1 @ C ) ))).
% 2.80/2.99  thf('17', plain,
% 2.80/2.99      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.80/2.99         ((v1_relat_1 @ X32)
% 2.80/2.99          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 2.80/2.99      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.80/2.99  thf('18', plain, ((v1_relat_1 @ sk_C_1)),
% 2.80/2.99      inference('sup-', [status(thm)], ['16', '17'])).
% 2.80/2.99  thf('19', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_tarski @ sk_A))),
% 2.80/2.99      inference('demod', [status(thm)], ['15', '18'])).
% 2.80/2.99  thf(l3_zfmisc_1, axiom,
% 2.80/2.99    (![A:$i,B:$i]:
% 2.80/2.99     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 2.80/2.99       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 2.80/2.99  thf('20', plain,
% 2.80/2.99      (![X14 : $i, X15 : $i]:
% 2.80/2.99         (((X15) = (k1_tarski @ X14))
% 2.80/2.99          | ((X15) = (k1_xboole_0))
% 2.80/2.99          | ~ (r1_tarski @ X15 @ (k1_tarski @ X14)))),
% 2.80/2.99      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 2.80/2.99  thf('21', plain,
% 2.80/2.99      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 2.80/2.99        | ((k1_relat_1 @ sk_C_1) = (k1_tarski @ sk_A)))),
% 2.80/2.99      inference('sup-', [status(thm)], ['19', '20'])).
% 2.80/2.99  thf(t14_funct_1, axiom,
% 2.80/2.99    (![A:$i,B:$i]:
% 2.80/2.99     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.80/2.99       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 2.80/2.99         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 2.80/2.99  thf('22', plain,
% 2.80/2.99      (![X30 : $i, X31 : $i]:
% 2.80/2.99         (((k1_relat_1 @ X31) != (k1_tarski @ X30))
% 2.80/2.99          | ((k2_relat_1 @ X31) = (k1_tarski @ (k1_funct_1 @ X31 @ X30)))
% 2.80/2.99          | ~ (v1_funct_1 @ X31)
% 2.80/2.99          | ~ (v1_relat_1 @ X31))),
% 2.80/2.99      inference('cnf', [status(esa)], [t14_funct_1])).
% 2.80/2.99  thf('23', plain,
% 2.80/2.99      (![X0 : $i]:
% 2.80/2.99         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C_1))
% 2.80/2.99          | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 2.80/2.99          | ~ (v1_relat_1 @ X0)
% 2.80/2.99          | ~ (v1_funct_1 @ X0)
% 2.80/2.99          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 2.80/2.99      inference('sup-', [status(thm)], ['21', '22'])).
% 2.80/2.99  thf('24', plain,
% 2.80/2.99      ((((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))
% 2.80/2.99        | ~ (v1_funct_1 @ sk_C_1)
% 2.80/2.99        | ~ (v1_relat_1 @ sk_C_1)
% 2.80/2.99        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 2.80/2.99      inference('eq_res', [status(thm)], ['23'])).
% 2.80/2.99  thf('25', plain, ((v1_funct_1 @ sk_C_1)),
% 2.80/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.80/2.99  thf('26', plain, ((v1_relat_1 @ sk_C_1)),
% 2.80/2.99      inference('sup-', [status(thm)], ['16', '17'])).
% 2.80/2.99  thf('27', plain,
% 2.80/2.99      ((((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))
% 2.80/2.99        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 2.80/2.99      inference('demod', [status(thm)], ['24', '25', '26'])).
% 2.80/2.99  thf('28', plain,
% 2.80/2.99      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 2.80/2.99         != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 2.80/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.80/2.99  thf('29', plain,
% 2.80/2.99      ((m1_subset_1 @ sk_C_1 @ 
% 2.80/2.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 2.80/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.80/2.99  thf(redefinition_k2_relset_1, axiom,
% 2.80/2.99    (![A:$i,B:$i,C:$i]:
% 2.80/2.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.80/2.99       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.80/2.99  thf('30', plain,
% 2.80/2.99      (![X42 : $i, X43 : $i, X44 : $i]:
% 2.80/2.99         (((k2_relset_1 @ X43 @ X44 @ X42) = (k2_relat_1 @ X42))
% 2.80/2.99          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44))))),
% 2.80/2.99      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.80/2.99  thf('31', plain,
% 2.80/2.99      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 2.80/2.99         = (k2_relat_1 @ sk_C_1))),
% 2.80/2.99      inference('sup-', [status(thm)], ['29', '30'])).
% 2.80/2.99  thf('32', plain,
% 2.80/2.99      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 2.80/2.99      inference('demod', [status(thm)], ['28', '31'])).
% 2.80/2.99  thf('33', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 2.80/2.99      inference('simplify_reflect-', [status(thm)], ['27', '32'])).
% 2.80/2.99  thf(t64_relat_1, axiom,
% 2.80/2.99    (![A:$i]:
% 2.80/2.99     ( ( v1_relat_1 @ A ) =>
% 2.80/2.99       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 2.80/2.99           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 2.80/2.99         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 2.80/2.99  thf('34', plain,
% 2.80/2.99      (![X29 : $i]:
% 2.80/2.99         (((k1_relat_1 @ X29) != (k1_xboole_0))
% 2.80/2.99          | ((X29) = (k1_xboole_0))
% 2.80/2.99          | ~ (v1_relat_1 @ X29))),
% 2.80/2.99      inference('cnf', [status(esa)], [t64_relat_1])).
% 2.80/2.99  thf('35', plain,
% 2.80/2.99      ((((k1_xboole_0) != (k1_xboole_0))
% 2.80/2.99        | ~ (v1_relat_1 @ sk_C_1)
% 2.80/2.99        | ((sk_C_1) = (k1_xboole_0)))),
% 2.80/2.99      inference('sup-', [status(thm)], ['33', '34'])).
% 2.80/2.99  thf('36', plain, ((v1_relat_1 @ sk_C_1)),
% 2.80/2.99      inference('sup-', [status(thm)], ['16', '17'])).
% 2.80/2.99  thf('37', plain,
% 2.80/2.99      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 2.80/2.99      inference('demod', [status(thm)], ['35', '36'])).
% 2.80/2.99  thf('38', plain, (((sk_C_1) = (k1_xboole_0))),
% 2.80/2.99      inference('simplify', [status(thm)], ['37'])).
% 2.80/2.99  thf(t4_subset_1, axiom,
% 2.80/2.99    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 2.80/2.99  thf('39', plain,
% 2.80/2.99      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 2.80/2.99      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.80/2.99  thf(t39_relset_1, axiom,
% 2.80/2.99    (![A:$i,B:$i,C:$i]:
% 2.80/2.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 2.80/2.99       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 2.80/2.99           ( k2_relset_1 @ B @ A @ C ) ) & 
% 2.80/2.99         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 2.80/2.99           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 2.80/2.99  thf('40', plain,
% 2.80/2.99      (![X49 : $i, X50 : $i, X51 : $i]:
% 2.80/2.99         (((k8_relset_1 @ X49 @ X50 @ X51 @ 
% 2.80/2.99            (k7_relset_1 @ X49 @ X50 @ X51 @ X49))
% 2.80/2.99            = (k1_relset_1 @ X49 @ X50 @ X51))
% 2.80/2.99          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50))))),
% 2.80/2.99      inference('cnf', [status(esa)], [t39_relset_1])).
% 2.80/2.99  thf('41', plain,
% 2.80/2.99      (![X0 : $i, X1 : $i]:
% 2.80/2.99         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ 
% 2.80/2.99           (k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X1))
% 2.80/2.99           = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 2.80/2.99      inference('sup-', [status(thm)], ['39', '40'])).
% 2.80/2.99  thf('42', plain,
% 2.80/2.99      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 2.80/2.99      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.80/2.99  thf(redefinition_k8_relset_1, axiom,
% 2.80/2.99    (![A:$i,B:$i,C:$i,D:$i]:
% 2.80/2.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.80/2.99       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 2.80/2.99  thf('43', plain,
% 2.80/2.99      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 2.80/2.99         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 2.80/2.99          | ((k8_relset_1 @ X46 @ X47 @ X45 @ X48) = (k10_relat_1 @ X45 @ X48)))),
% 2.80/2.99      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 2.80/2.99  thf('44', plain,
% 2.80/2.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.80/2.99         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 2.80/2.99           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 2.80/2.99      inference('sup-', [status(thm)], ['42', '43'])).
% 2.80/2.99  thf('45', plain,
% 2.80/2.99      (![X0 : $i, X1 : $i]:
% 2.80/2.99         ((k10_relat_1 @ k1_xboole_0 @ 
% 2.80/2.99           (k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X1))
% 2.80/2.99           = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 2.80/2.99      inference('demod', [status(thm)], ['41', '44'])).
% 2.80/2.99  thf('46', plain,
% 2.80/2.99      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 2.80/2.99      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.80/2.99  thf(dt_k8_relset_1, axiom,
% 2.80/2.99    (![A:$i,B:$i,C:$i,D:$i]:
% 2.80/2.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.80/2.99       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.80/2.99  thf('47', plain,
% 2.80/2.99      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 2.80/2.99         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 2.80/2.99          | (m1_subset_1 @ (k8_relset_1 @ X39 @ X40 @ X38 @ X41) @ 
% 2.80/2.99             (k1_zfmisc_1 @ X39)))),
% 2.80/2.99      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 2.80/2.99  thf('48', plain,
% 2.80/2.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.80/2.99         (m1_subset_1 @ (k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) @ 
% 2.80/2.99          (k1_zfmisc_1 @ X1))),
% 2.80/2.99      inference('sup-', [status(thm)], ['46', '47'])).
% 2.80/2.99  thf('49', plain,
% 2.80/2.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.80/2.99         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 2.80/2.99           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 2.80/2.99      inference('sup-', [status(thm)], ['42', '43'])).
% 2.80/2.99  thf('50', plain,
% 2.80/2.99      (![X1 : $i, X2 : $i]:
% 2.80/2.99         (m1_subset_1 @ (k10_relat_1 @ k1_xboole_0 @ X2) @ (k1_zfmisc_1 @ X1))),
% 2.80/2.99      inference('demod', [status(thm)], ['48', '49'])).
% 2.80/2.99  thf(t3_subset, axiom,
% 2.80/2.99    (![A:$i,B:$i]:
% 2.80/2.99     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.80/2.99  thf('51', plain,
% 2.80/2.99      (![X18 : $i, X19 : $i]:
% 2.80/2.99         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 2.80/2.99      inference('cnf', [status(esa)], [t3_subset])).
% 2.80/2.99  thf('52', plain,
% 2.80/2.99      (![X0 : $i, X1 : $i]: (r1_tarski @ (k10_relat_1 @ k1_xboole_0 @ X1) @ X0)),
% 2.80/2.99      inference('sup-', [status(thm)], ['50', '51'])).
% 2.80/2.99  thf('53', plain,
% 2.80/2.99      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 2.80/2.99      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.80/2.99  thf('54', plain,
% 2.80/2.99      (![X18 : $i, X19 : $i]:
% 2.80/2.99         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 2.80/2.99      inference('cnf', [status(esa)], [t3_subset])).
% 2.80/2.99  thf('55', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.80/2.99      inference('sup-', [status(thm)], ['53', '54'])).
% 2.80/2.99  thf(d10_xboole_0, axiom,
% 2.80/2.99    (![A:$i,B:$i]:
% 2.80/2.99     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.80/2.99  thf('56', plain,
% 2.80/2.99      (![X5 : $i, X7 : $i]:
% 2.80/2.99         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 2.80/2.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.80/2.99  thf('57', plain,
% 2.80/2.99      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.80/2.99      inference('sup-', [status(thm)], ['55', '56'])).
% 2.80/2.99  thf('58', plain,
% 2.80/2.99      (![X0 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.80/2.99      inference('sup-', [status(thm)], ['52', '57'])).
% 2.80/2.99  thf('59', plain,
% 2.80/2.99      (![X0 : $i, X1 : $i]:
% 2.80/2.99         ((k1_xboole_0) = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 2.80/2.99      inference('demod', [status(thm)], ['45', '58'])).
% 2.80/2.99  thf('60', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 2.80/2.99      inference('demod', [status(thm)], ['10', '38', '59'])).
% 2.80/2.99  thf('61', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 2.80/2.99      inference('simplify_reflect-', [status(thm)], ['27', '32'])).
% 2.80/2.99  thf('62', plain,
% 2.80/2.99      (![X30 : $i, X31 : $i]:
% 2.80/2.99         (((k1_relat_1 @ X31) != (k1_tarski @ X30))
% 2.80/2.99          | ((k2_relat_1 @ X31) = (k1_tarski @ (k1_funct_1 @ X31 @ X30)))
% 2.80/2.99          | ~ (v1_funct_1 @ X31)
% 2.80/2.99          | ~ (v1_relat_1 @ X31))),
% 2.80/2.99      inference('cnf', [status(esa)], [t14_funct_1])).
% 2.80/2.99  thf('63', plain,
% 2.80/2.99      (![X0 : $i]:
% 2.80/2.99         (((k1_xboole_0) != (k1_tarski @ X0))
% 2.80/2.99          | ~ (v1_relat_1 @ sk_C_1)
% 2.80/2.99          | ~ (v1_funct_1 @ sk_C_1)
% 2.80/2.99          | ((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ X0))))),
% 2.80/2.99      inference('sup-', [status(thm)], ['61', '62'])).
% 2.80/2.99  thf('64', plain, ((v1_relat_1 @ sk_C_1)),
% 2.80/2.99      inference('sup-', [status(thm)], ['16', '17'])).
% 2.80/2.99  thf('65', plain, ((v1_funct_1 @ sk_C_1)),
% 2.80/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.80/2.99  thf('66', plain,
% 2.80/2.99      (![X0 : $i]:
% 2.80/2.99         (((k1_xboole_0) != (k1_tarski @ X0))
% 2.80/2.99          | ((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ X0))))),
% 2.80/2.99      inference('demod', [status(thm)], ['63', '64', '65'])).
% 2.80/2.99  thf('67', plain, (((sk_C_1) = (k1_xboole_0))),
% 2.80/2.99      inference('simplify', [status(thm)], ['37'])).
% 2.80/2.99  thf('68', plain, (((sk_C_1) = (k1_xboole_0))),
% 2.80/2.99      inference('simplify', [status(thm)], ['37'])).
% 2.80/2.99  thf('69', plain,
% 2.80/2.99      (![X0 : $i]:
% 2.80/2.99         (((k1_xboole_0) != (k1_tarski @ X0))
% 2.80/2.99          | ((k2_relat_1 @ k1_xboole_0)
% 2.80/2.99              = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 2.80/2.99      inference('demod', [status(thm)], ['66', '67', '68'])).
% 2.80/2.99  thf('70', plain,
% 2.80/2.99      ((((k1_xboole_0) != (k1_xboole_0))
% 2.80/2.99        | ((k2_relat_1 @ k1_xboole_0)
% 2.80/2.99            = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A))))),
% 2.80/2.99      inference('sup-', [status(thm)], ['60', '69'])).
% 2.80/2.99  thf('71', plain,
% 2.80/2.99      (((k2_relat_1 @ k1_xboole_0)
% 2.80/2.99         = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 2.80/2.99      inference('simplify', [status(thm)], ['70'])).
% 2.80/2.99  thf('72', plain,
% 2.80/2.99      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 2.80/2.99      inference('demod', [status(thm)], ['28', '31'])).
% 2.80/2.99  thf('73', plain, (((sk_C_1) = (k1_xboole_0))),
% 2.80/2.99      inference('simplify', [status(thm)], ['37'])).
% 2.80/2.99  thf('74', plain, (((sk_C_1) = (k1_xboole_0))),
% 2.80/2.99      inference('simplify', [status(thm)], ['37'])).
% 2.80/2.99  thf('75', plain,
% 2.80/2.99      (((k2_relat_1 @ k1_xboole_0)
% 2.80/2.99         != (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 2.80/2.99      inference('demod', [status(thm)], ['72', '73', '74'])).
% 2.80/2.99  thf('76', plain, ($false),
% 2.80/2.99      inference('simplify_reflect-', [status(thm)], ['71', '75'])).
% 2.80/2.99  
% 2.80/2.99  % SZS output end Refutation
% 2.80/2.99  
% 2.80/3.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

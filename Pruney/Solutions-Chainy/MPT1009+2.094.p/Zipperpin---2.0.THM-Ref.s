%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rh18ZCfYfg

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:02 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 234 expanded)
%              Number of leaves         :   36 (  87 expanded)
%              Depth                    :   14
%              Number of atoms          :  673 (3274 expanded)
%              Number of equality atoms :   51 ( 183 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( ( k9_relat_1 @ X6 @ ( k1_relat_1 @ X6 ) )
        = ( k2_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t147_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X7 @ X8 ) @ ( k9_relat_1 @ X7 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t147_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

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

thf('4',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k7_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k9_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_D @ ( k1_tarski @ sk_A ) @ sk_B ),
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

thf('11',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('15',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('16',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['12','19','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','23'])).

thf('25',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['12','19','22'])).

thf(t62_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( k1_tarski @ X32 ) @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X32 ) @ X30 ) ) )
      | ( ( k2_relset_1 @ ( k1_tarski @ X32 ) @ X30 @ X31 )
        = ( k1_tarski @ ( k1_funct_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[t62_funct_2])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) )
      | ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ X0 @ X1 )
        = ( k1_tarski @ ( k1_funct_1 @ X1 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( k1_tarski @ sk_A ) @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['12','19','22'])).

thf('29',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['12','19','22'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ X0 @ X1 )
        = ( k1_tarski @ ( k1_funct_1 @ X1 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( k1_relat_1 @ sk_D ) @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_B )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_2 @ sk_D @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['12','19','22'])).

thf('35',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('38',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['12','19','22'])).

thf('40',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32','35','40'])).

thf('42',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['8','43'])).

thf('45',plain,(
    ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('47',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('48',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['45','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rh18ZCfYfg
% 0.13/0.37  % Computer   : n018.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 19:48:42 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.71/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.71/0.89  % Solved by: fo/fo7.sh
% 0.71/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.89  % done 214 iterations in 0.400s
% 0.71/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.71/0.89  % SZS output start Refutation
% 0.71/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.71/0.89  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.71/0.89  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.71/0.89  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.71/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.89  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.71/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.71/0.89  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.71/0.89  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.71/0.89  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.71/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.71/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.71/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.71/0.89  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.71/0.89  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.71/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.71/0.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.71/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.71/0.89  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.71/0.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.71/0.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.71/0.89  thf(sk_D_type, type, sk_D: $i).
% 0.71/0.89  thf(t146_relat_1, axiom,
% 0.71/0.89    (![A:$i]:
% 0.71/0.89     ( ( v1_relat_1 @ A ) =>
% 0.71/0.89       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.71/0.89  thf('0', plain,
% 0.71/0.89      (![X6 : $i]:
% 0.71/0.89         (((k9_relat_1 @ X6 @ (k1_relat_1 @ X6)) = (k2_relat_1 @ X6))
% 0.71/0.89          | ~ (v1_relat_1 @ X6))),
% 0.71/0.89      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.71/0.89  thf(t147_relat_1, axiom,
% 0.71/0.89    (![A:$i,B:$i]:
% 0.71/0.89     ( ( v1_relat_1 @ B ) =>
% 0.71/0.89       ( r1_tarski @
% 0.71/0.89         ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ))).
% 0.71/0.89  thf('1', plain,
% 0.71/0.89      (![X7 : $i, X8 : $i]:
% 0.71/0.89         ((r1_tarski @ (k9_relat_1 @ X7 @ X8) @ 
% 0.71/0.89           (k9_relat_1 @ X7 @ (k1_relat_1 @ X7)))
% 0.71/0.89          | ~ (v1_relat_1 @ X7))),
% 0.71/0.89      inference('cnf', [status(esa)], [t147_relat_1])).
% 0.71/0.89  thf('2', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i]:
% 0.71/0.89         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0))
% 0.71/0.89          | ~ (v1_relat_1 @ X0)
% 0.71/0.89          | ~ (v1_relat_1 @ X0))),
% 0.71/0.89      inference('sup+', [status(thm)], ['0', '1'])).
% 0.71/0.89  thf('3', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i]:
% 0.71/0.89         (~ (v1_relat_1 @ X0)
% 0.71/0.89          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0)))),
% 0.71/0.89      inference('simplify', [status(thm)], ['2'])).
% 0.71/0.89  thf(t64_funct_2, conjecture,
% 0.71/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.89     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.71/0.89         ( m1_subset_1 @
% 0.71/0.89           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.71/0.89       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.71/0.89         ( r1_tarski @
% 0.71/0.89           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.71/0.89           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.71/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.89    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.89        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.71/0.89            ( m1_subset_1 @
% 0.71/0.89              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.71/0.89          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.71/0.89            ( r1_tarski @
% 0.71/0.89              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.71/0.89              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.71/0.89    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.71/0.89  thf('4', plain,
% 0.71/0.89      (~ (r1_tarski @ 
% 0.71/0.89          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.71/0.89          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('5', plain,
% 0.71/0.89      ((m1_subset_1 @ sk_D @ 
% 0.71/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf(redefinition_k7_relset_1, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.89       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.71/0.89  thf('6', plain,
% 0.71/0.89      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.71/0.89         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.71/0.89          | ((k7_relset_1 @ X19 @ X20 @ X18 @ X21) = (k9_relat_1 @ X18 @ X21)))),
% 0.71/0.89      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.71/0.89  thf('7', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.71/0.89           = (k9_relat_1 @ sk_D @ X0))),
% 0.71/0.89      inference('sup-', [status(thm)], ['5', '6'])).
% 0.71/0.89  thf('8', plain,
% 0.71/0.89      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.71/0.89          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.71/0.89      inference('demod', [status(thm)], ['4', '7'])).
% 0.71/0.89  thf('9', plain,
% 0.71/0.89      ((m1_subset_1 @ sk_D @ 
% 0.71/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('10', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf(d1_funct_2, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i]:
% 0.71/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.89       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.71/0.89           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.71/0.89             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.71/0.89         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.71/0.89           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.71/0.89             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.71/0.89  thf(zf_stmt_1, axiom,
% 0.71/0.89    (![C:$i,B:$i,A:$i]:
% 0.71/0.89     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.71/0.89       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.71/0.89  thf('11', plain,
% 0.71/0.89      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.71/0.89         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.71/0.89          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.71/0.89          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.71/0.89  thf('12', plain,
% 0.71/0.89      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.71/0.89        | ((k1_tarski @ sk_A)
% 0.71/0.89            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['10', '11'])).
% 0.71/0.89  thf(zf_stmt_2, axiom,
% 0.71/0.89    (![B:$i,A:$i]:
% 0.71/0.89     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.71/0.89       ( zip_tseitin_0 @ B @ A ) ))).
% 0.71/0.89  thf('13', plain,
% 0.71/0.89      (![X22 : $i, X23 : $i]:
% 0.71/0.89         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.71/0.89  thf('14', plain,
% 0.71/0.89      ((m1_subset_1 @ sk_D @ 
% 0.71/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.71/0.89  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.71/0.89  thf(zf_stmt_5, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i]:
% 0.71/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.89       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.71/0.89         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.71/0.89           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.71/0.89             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.71/0.89  thf('15', plain,
% 0.71/0.89      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.71/0.89         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.71/0.89          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.71/0.89          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.71/0.89  thf('16', plain,
% 0.71/0.89      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.71/0.89        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['14', '15'])).
% 0.71/0.89  thf('17', plain,
% 0.71/0.89      ((((sk_B) = (k1_xboole_0))
% 0.71/0.89        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['13', '16'])).
% 0.71/0.89  thf('18', plain, (((sk_B) != (k1_xboole_0))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('19', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.71/0.89      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.71/0.89  thf('20', plain,
% 0.71/0.89      ((m1_subset_1 @ sk_D @ 
% 0.71/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf(redefinition_k1_relset_1, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i]:
% 0.71/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.89       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.71/0.89  thf('21', plain,
% 0.71/0.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.71/0.89         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.71/0.89          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.71/0.89      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.71/0.89  thf('22', plain,
% 0.71/0.89      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.71/0.89      inference('sup-', [status(thm)], ['20', '21'])).
% 0.71/0.89  thf('23', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.71/0.89      inference('demod', [status(thm)], ['12', '19', '22'])).
% 0.71/0.89  thf('24', plain,
% 0.71/0.89      ((m1_subset_1 @ sk_D @ 
% 0.71/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.71/0.89      inference('demod', [status(thm)], ['9', '23'])).
% 0.71/0.89  thf('25', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.71/0.89      inference('demod', [status(thm)], ['12', '19', '22'])).
% 0.71/0.89  thf(t62_funct_2, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i]:
% 0.71/0.89     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.71/0.89         ( m1_subset_1 @
% 0.71/0.89           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.71/0.89       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.71/0.89         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.71/0.89           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.71/0.89  thf('26', plain,
% 0.71/0.89      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.71/0.89         (((X30) = (k1_xboole_0))
% 0.71/0.89          | ~ (v1_funct_1 @ X31)
% 0.71/0.89          | ~ (v1_funct_2 @ X31 @ (k1_tarski @ X32) @ X30)
% 0.71/0.89          | ~ (m1_subset_1 @ X31 @ 
% 0.71/0.89               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ X32) @ X30)))
% 0.71/0.89          | ((k2_relset_1 @ (k1_tarski @ X32) @ X30 @ X31)
% 0.71/0.89              = (k1_tarski @ (k1_funct_1 @ X31 @ X32))))),
% 0.71/0.89      inference('cnf', [status(esa)], [t62_funct_2])).
% 0.71/0.89  thf('27', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i]:
% 0.71/0.89         (~ (m1_subset_1 @ X1 @ 
% 0.71/0.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0)))
% 0.71/0.89          | ((k2_relset_1 @ (k1_tarski @ sk_A) @ X0 @ X1)
% 0.71/0.89              = (k1_tarski @ (k1_funct_1 @ X1 @ sk_A)))
% 0.71/0.89          | ~ (v1_funct_2 @ X1 @ (k1_tarski @ sk_A) @ X0)
% 0.71/0.89          | ~ (v1_funct_1 @ X1)
% 0.71/0.89          | ((X0) = (k1_xboole_0)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['25', '26'])).
% 0.71/0.89  thf('28', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.71/0.89      inference('demod', [status(thm)], ['12', '19', '22'])).
% 0.71/0.89  thf('29', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.71/0.89      inference('demod', [status(thm)], ['12', '19', '22'])).
% 0.71/0.89  thf('30', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i]:
% 0.71/0.89         (~ (m1_subset_1 @ X1 @ 
% 0.71/0.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0)))
% 0.71/0.89          | ((k2_relset_1 @ (k1_relat_1 @ sk_D) @ X0 @ X1)
% 0.71/0.89              = (k1_tarski @ (k1_funct_1 @ X1 @ sk_A)))
% 0.71/0.89          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ sk_D) @ X0)
% 0.71/0.89          | ~ (v1_funct_1 @ X1)
% 0.71/0.89          | ((X0) = (k1_xboole_0)))),
% 0.71/0.89      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.71/0.89  thf('31', plain,
% 0.71/0.89      ((((sk_B) = (k1_xboole_0))
% 0.71/0.89        | ~ (v1_funct_1 @ sk_D)
% 0.71/0.89        | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_B)
% 0.71/0.89        | ((k2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D)
% 0.71/0.89            = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A))))),
% 0.71/0.89      inference('sup-', [status(thm)], ['24', '30'])).
% 0.71/0.89  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('33', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('34', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.71/0.89      inference('demod', [status(thm)], ['12', '19', '22'])).
% 0.71/0.89  thf('35', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.71/0.89      inference('demod', [status(thm)], ['33', '34'])).
% 0.71/0.89  thf('36', plain,
% 0.71/0.89      ((m1_subset_1 @ sk_D @ 
% 0.71/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf(redefinition_k2_relset_1, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i]:
% 0.71/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.89       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.71/0.89  thf('37', plain,
% 0.71/0.89      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.71/0.89         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.71/0.89          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.71/0.89      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.71/0.89  thf('38', plain,
% 0.71/0.89      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.71/0.89      inference('sup-', [status(thm)], ['36', '37'])).
% 0.71/0.89  thf('39', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.71/0.89      inference('demod', [status(thm)], ['12', '19', '22'])).
% 0.71/0.89  thf('40', plain,
% 0.71/0.89      (((k2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.71/0.89      inference('demod', [status(thm)], ['38', '39'])).
% 0.71/0.89  thf('41', plain,
% 0.71/0.89      ((((sk_B) = (k1_xboole_0))
% 0.71/0.89        | ((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A))))),
% 0.71/0.89      inference('demod', [status(thm)], ['31', '32', '35', '40'])).
% 0.71/0.89  thf('42', plain, (((sk_B) != (k1_xboole_0))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('43', plain,
% 0.71/0.89      (((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.71/0.89      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.71/0.89  thf('44', plain,
% 0.71/0.89      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.71/0.89      inference('demod', [status(thm)], ['8', '43'])).
% 0.71/0.89  thf('45', plain, (~ (v1_relat_1 @ sk_D)),
% 0.71/0.89      inference('sup-', [status(thm)], ['3', '44'])).
% 0.71/0.89  thf('46', plain,
% 0.71/0.89      ((m1_subset_1 @ sk_D @ 
% 0.71/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf(cc1_relset_1, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i]:
% 0.71/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.89       ( v1_relat_1 @ C ) ))).
% 0.71/0.89  thf('47', plain,
% 0.71/0.89      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.71/0.89         ((v1_relat_1 @ X9)
% 0.71/0.89          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.71/0.89      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.71/0.89  thf('48', plain, ((v1_relat_1 @ sk_D)),
% 0.71/0.89      inference('sup-', [status(thm)], ['46', '47'])).
% 0.71/0.89  thf('49', plain, ($false), inference('demod', [status(thm)], ['45', '48'])).
% 0.71/0.89  
% 0.71/0.89  % SZS output end Refutation
% 0.71/0.89  
% 0.71/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

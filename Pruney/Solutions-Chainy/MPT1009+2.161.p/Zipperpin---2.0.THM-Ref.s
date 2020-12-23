%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jM143JJsZ3

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:12 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 267 expanded)
%              Number of leaves         :   39 (  97 expanded)
%              Depth                    :   14
%              Number of atoms          :  801 (3713 expanded)
%              Number of equality atoms :   62 ( 205 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( ( k7_relset_1 @ X18 @ X19 @ X17 @ X20 )
        = ( k9_relat_1 @ X17 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('11',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('17',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k1_relat_1 @ X10 )
       != ( k1_tarski @ X9 ) )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_tarski @ ( k1_funct_1 @ X10 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference(eq_res,[status(thm)],['20'])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','27'])).

thf('29',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['4','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t39_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
          = ( k2_relset_1 @ B @ A @ C ) )
        & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
          = ( k1_relset_1 @ B @ A @ C ) ) ) ) )).

thf('33',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k7_relset_1 @ X21 @ X22 @ X23 @ ( k8_relset_1 @ X21 @ X22 @ X23 @ X22 ) )
        = ( k2_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t39_relset_1])).

thf('34',plain,
    ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ ( k8_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_B ) )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('36',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('37',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf('39',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ ( k8_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_B ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('42',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k9_relat_1 @ sk_D @ ( k8_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_B ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t48_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf('46',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X34 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X34 ) ) )
      | ( ( k8_relset_1 @ X32 @ X34 @ X33 @ X34 )
        = X32 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('47',plain,
    ( ( ( k8_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_B )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_2 @ sk_D @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf('50',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k8_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_B )
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','50','51'])).

thf('53',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k8_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_B )
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k9_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['44','54'])).

thf(t147_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) )).

thf('56',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X7 @ X8 ) @ ( k9_relat_1 @ X7 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t147_relat_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['25','26'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['29','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jM143JJsZ3
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.71  % Solved by: fo/fo7.sh
% 0.46/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.71  % done 117 iterations in 0.253s
% 0.46/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.71  % SZS output start Refutation
% 0.46/0.71  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.46/0.71  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.46/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.71  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.71  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.71  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.46/0.71  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.46/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.71  thf(t64_funct_2, conjecture,
% 0.46/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.71     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.46/0.71         ( m1_subset_1 @
% 0.46/0.71           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.46/0.71       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.46/0.71         ( r1_tarski @
% 0.46/0.71           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.46/0.71           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.46/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.71    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.71        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.46/0.71            ( m1_subset_1 @
% 0.46/0.71              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.46/0.71          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.46/0.71            ( r1_tarski @
% 0.46/0.71              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.46/0.71              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.46/0.71    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.46/0.71  thf('0', plain,
% 0.46/0.71      (~ (r1_tarski @ 
% 0.46/0.71          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.46/0.71          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('1', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_D @ 
% 0.46/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(redefinition_k7_relset_1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.71       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.46/0.71  thf('2', plain,
% 0.46/0.71      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.46/0.71          | ((k7_relset_1 @ X18 @ X19 @ X17 @ X20) = (k9_relat_1 @ X17 @ X20)))),
% 0.46/0.71      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.46/0.71  thf('3', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.46/0.71           = (k9_relat_1 @ sk_D @ X0))),
% 0.46/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.71  thf('4', plain,
% 0.46/0.71      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.46/0.71          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.46/0.71      inference('demod', [status(thm)], ['0', '3'])).
% 0.46/0.71  thf('5', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(d1_funct_2, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.71       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.71           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.46/0.71             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.71         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.71           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.46/0.71             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.71  thf(zf_stmt_1, axiom,
% 0.46/0.71    (![C:$i,B:$i,A:$i]:
% 0.46/0.71     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.46/0.71       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.71  thf('6', plain,
% 0.46/0.71      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.71         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.46/0.71          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 0.46/0.71          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.71  thf('7', plain,
% 0.46/0.71      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.71        | ((k1_tarski @ sk_A)
% 0.46/0.71            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.71  thf(zf_stmt_2, axiom,
% 0.46/0.71    (![B:$i,A:$i]:
% 0.46/0.71     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.71       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.71  thf('8', plain,
% 0.46/0.71      (![X24 : $i, X25 : $i]:
% 0.46/0.71         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.71  thf('9', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_D @ 
% 0.46/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.71  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.71  thf(zf_stmt_5, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.71       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.46/0.71         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.71           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.71             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.46/0.71  thf('10', plain,
% 0.46/0.71      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.71         (~ (zip_tseitin_0 @ X29 @ X30)
% 0.46/0.71          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 0.46/0.71          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.71  thf('11', plain,
% 0.46/0.71      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.71        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.71  thf('12', plain,
% 0.46/0.71      ((((sk_B) = (k1_xboole_0))
% 0.46/0.71        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['8', '11'])).
% 0.46/0.71  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('14', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.46/0.71      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.46/0.71  thf('15', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_D @ 
% 0.46/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.71       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.71  thf('16', plain,
% 0.46/0.71      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.71         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.46/0.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.46/0.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.71  thf('17', plain,
% 0.46/0.71      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.46/0.71      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.71  thf('18', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.46/0.71      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.46/0.71  thf(t14_funct_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.71       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.46/0.71         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.46/0.71  thf('19', plain,
% 0.46/0.71      (![X9 : $i, X10 : $i]:
% 0.46/0.71         (((k1_relat_1 @ X10) != (k1_tarski @ X9))
% 0.46/0.71          | ((k2_relat_1 @ X10) = (k1_tarski @ (k1_funct_1 @ X10 @ X9)))
% 0.46/0.71          | ~ (v1_funct_1 @ X10)
% 0.46/0.71          | ~ (v1_relat_1 @ X10))),
% 0.46/0.71      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.46/0.71  thf('20', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.46/0.71          | ~ (v1_relat_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.71  thf('21', plain,
% 0.46/0.71      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.46/0.71        | ~ (v1_funct_1 @ sk_D)
% 0.46/0.71        | ~ (v1_relat_1 @ sk_D))),
% 0.46/0.71      inference('eq_res', [status(thm)], ['20'])).
% 0.46/0.71  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('23', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_D @ 
% 0.46/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(cc2_relat_1, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( v1_relat_1 @ A ) =>
% 0.46/0.71       ( ![B:$i]:
% 0.46/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.71  thf('24', plain,
% 0.46/0.71      (![X3 : $i, X4 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.46/0.71          | (v1_relat_1 @ X3)
% 0.46/0.71          | ~ (v1_relat_1 @ X4))),
% 0.46/0.71      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.71  thf('25', plain,
% 0.46/0.71      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.46/0.71        | (v1_relat_1 @ sk_D))),
% 0.46/0.71      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.71  thf(fc6_relat_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.71  thf('26', plain,
% 0.46/0.71      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.46/0.71      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.71  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.71      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.71  thf('28', plain,
% 0.46/0.71      (((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.46/0.71      inference('demod', [status(thm)], ['21', '22', '27'])).
% 0.46/0.71  thf('29', plain,
% 0.46/0.71      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.46/0.71      inference('demod', [status(thm)], ['4', '28'])).
% 0.46/0.71  thf('30', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_D @ 
% 0.46/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('31', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.46/0.71      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.46/0.71  thf('32', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_D @ 
% 0.46/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.46/0.71      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.71  thf(t39_relset_1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.46/0.71       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.46/0.71           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.46/0.71         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.46/0.71           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.46/0.71  thf('33', plain,
% 0.46/0.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.71         (((k7_relset_1 @ X21 @ X22 @ X23 @ 
% 0.46/0.71            (k8_relset_1 @ X21 @ X22 @ X23 @ X22))
% 0.46/0.71            = (k2_relset_1 @ X21 @ X22 @ X23))
% 0.46/0.71          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.46/0.71      inference('cnf', [status(esa)], [t39_relset_1])).
% 0.46/0.71  thf('34', plain,
% 0.46/0.71      (((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ 
% 0.46/0.71         (k8_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_B))
% 0.46/0.71         = (k2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D))),
% 0.46/0.71      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.71  thf('35', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_D @ 
% 0.46/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.71       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.71  thf('36', plain,
% 0.46/0.71      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.71         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.46/0.71          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.46/0.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.71  thf('37', plain,
% 0.46/0.71      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.46/0.71      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.71  thf('38', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.46/0.71      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.46/0.71  thf('39', plain,
% 0.46/0.71      (((k2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.46/0.71      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.71  thf('40', plain,
% 0.46/0.71      (((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ 
% 0.46/0.71         (k8_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_B))
% 0.46/0.71         = (k2_relat_1 @ sk_D))),
% 0.46/0.71      inference('demod', [status(thm)], ['34', '39'])).
% 0.46/0.71  thf('41', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.46/0.71           = (k9_relat_1 @ sk_D @ X0))),
% 0.46/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.71  thf('42', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.46/0.71      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.46/0.71  thf('43', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.46/0.71           = (k9_relat_1 @ sk_D @ X0))),
% 0.46/0.71      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.71  thf('44', plain,
% 0.46/0.71      (((k9_relat_1 @ sk_D @ 
% 0.46/0.71         (k8_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_B))
% 0.46/0.71         = (k2_relat_1 @ sk_D))),
% 0.46/0.71      inference('demod', [status(thm)], ['40', '43'])).
% 0.46/0.71  thf('45', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_D @ 
% 0.46/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.55/0.71      inference('demod', [status(thm)], ['30', '31'])).
% 0.55/0.71  thf(t48_funct_2, axiom,
% 0.55/0.71    (![A:$i,B:$i,C:$i]:
% 0.55/0.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.55/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.71       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.55/0.71         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 0.55/0.71  thf('46', plain,
% 0.55/0.71      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.55/0.71         (((X34) = (k1_xboole_0))
% 0.55/0.71          | ~ (v1_funct_1 @ X33)
% 0.55/0.71          | ~ (v1_funct_2 @ X33 @ X32 @ X34)
% 0.55/0.71          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X34)))
% 0.55/0.71          | ((k8_relset_1 @ X32 @ X34 @ X33 @ X34) = (X32)))),
% 0.55/0.71      inference('cnf', [status(esa)], [t48_funct_2])).
% 0.55/0.71  thf('47', plain,
% 0.55/0.71      ((((k8_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_B)
% 0.55/0.71          = (k1_relat_1 @ sk_D))
% 0.55/0.71        | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_B)
% 0.55/0.71        | ~ (v1_funct_1 @ sk_D)
% 0.55/0.71        | ((sk_B) = (k1_xboole_0)))),
% 0.55/0.71      inference('sup-', [status(thm)], ['45', '46'])).
% 0.55/0.71  thf('48', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.55/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.71  thf('49', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.55/0.71      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.55/0.71  thf('50', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.55/0.71      inference('demod', [status(thm)], ['48', '49'])).
% 0.55/0.71  thf('51', plain, ((v1_funct_1 @ sk_D)),
% 0.55/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.71  thf('52', plain,
% 0.55/0.71      ((((k8_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_B)
% 0.55/0.71          = (k1_relat_1 @ sk_D))
% 0.55/0.71        | ((sk_B) = (k1_xboole_0)))),
% 0.55/0.71      inference('demod', [status(thm)], ['47', '50', '51'])).
% 0.55/0.71  thf('53', plain, (((sk_B) != (k1_xboole_0))),
% 0.55/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.71  thf('54', plain,
% 0.55/0.71      (((k8_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_B)
% 0.55/0.71         = (k1_relat_1 @ sk_D))),
% 0.55/0.71      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 0.55/0.71  thf('55', plain,
% 0.55/0.71      (((k9_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)) = (k2_relat_1 @ sk_D))),
% 0.55/0.71      inference('demod', [status(thm)], ['44', '54'])).
% 0.55/0.71  thf(t147_relat_1, axiom,
% 0.55/0.71    (![A:$i,B:$i]:
% 0.55/0.71     ( ( v1_relat_1 @ B ) =>
% 0.55/0.71       ( r1_tarski @
% 0.55/0.71         ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ))).
% 0.55/0.71  thf('56', plain,
% 0.55/0.71      (![X7 : $i, X8 : $i]:
% 0.55/0.71         ((r1_tarski @ (k9_relat_1 @ X7 @ X8) @ 
% 0.55/0.71           (k9_relat_1 @ X7 @ (k1_relat_1 @ X7)))
% 0.55/0.71          | ~ (v1_relat_1 @ X7))),
% 0.55/0.71      inference('cnf', [status(esa)], [t147_relat_1])).
% 0.55/0.71  thf('57', plain,
% 0.55/0.71      (![X0 : $i]:
% 0.55/0.71         ((r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))
% 0.55/0.71          | ~ (v1_relat_1 @ sk_D))),
% 0.55/0.71      inference('sup+', [status(thm)], ['55', '56'])).
% 0.55/0.71  thf('58', plain, ((v1_relat_1 @ sk_D)),
% 0.55/0.71      inference('demod', [status(thm)], ['25', '26'])).
% 0.55/0.71  thf('59', plain,
% 0.55/0.71      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))),
% 0.55/0.71      inference('demod', [status(thm)], ['57', '58'])).
% 0.55/0.71  thf('60', plain, ($false), inference('demod', [status(thm)], ['29', '59'])).
% 0.55/0.71  
% 0.55/0.71  % SZS output end Refutation
% 0.55/0.71  
% 0.55/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

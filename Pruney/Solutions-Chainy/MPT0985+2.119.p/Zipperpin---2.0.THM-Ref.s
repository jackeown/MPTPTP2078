%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.M4eGpKC9Pk

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:43 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :  293 (37894 expanded)
%              Number of leaves         :   36 (10716 expanded)
%              Depth                    :   32
%              Number of atoms          : 2467 (585610 expanded)
%              Number of equality atoms :  159 (33422 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('7',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('12',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('21',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k2_relset_1 @ k1_xboole_0 @ X0 @ X1 )
        = ( k2_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( ( k2_relset_1 @ k1_xboole_0 @ X0 @ sk_C )
        = ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('27',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( ( k2_relset_1 @ k1_xboole_0 @ X0 @ sk_C )
        = sk_B ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('32',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X14 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ ( k2_relset_1 @ k1_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( m1_subset_1 @ ( k2_relset_1 @ k1_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ X0 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ sk_C @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( r1_tarski @ sk_C @ sk_B ) ) ),
    inference(eq_fact,[status(thm)],['46'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( r1_tarski @ sk_B @ sk_C )
      | ( sk_B = sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( sk_B = sk_C )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','49'])).

thf('51',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('52',plain,
    ( ( sk_B = sk_C )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('54',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( sk_B = sk_C ) ),
    inference(clc,[status(thm)],['52','53'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('56',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('57',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('58',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('59',plain,(
    ! [X31: $i] :
      ( ( v1_funct_2 @ X31 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ( sk_B = sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['54','66'])).

thf('68',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['27','28'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('70',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = sk_C ) ),
    inference(demod,[status(thm)],['67','68','71','72','73'])).

thf('75',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['1','76'])).

thf('78',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('79',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('80',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('81',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('83',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_B ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('86',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('88',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['27','28'])).

thf('89',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('91',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('92',plain,
    ( ( v1_relat_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('97',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['86','89','92','95','98'])).

thf('100',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['1','76'])).

thf('101',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('103',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['77','101','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('105',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('106',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('107',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('112',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('113',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('114',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('115',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('116',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X31: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('121',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('126',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['119','126'])).

thf('128',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['114','127'])).

thf('129',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('130',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['113','131'])).

thf('133',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('134',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ X0 )
        | ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v2_funct_1 @ sk_C )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['112','135'])).

thf('137',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['27','28'])).

thf('138',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('139',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_B @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['136','137','138','139','140'])).

thf('142',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('143',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('145',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('147',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('148',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('149',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('150',plain,(
    ! [X31: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['148','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['147','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['146','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['145','157'])).

thf('159',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['27','28'])).

thf('160',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('161',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['158','159','160','161','162'])).

thf('164',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['111','163'])).

thf('165',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('166',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['110','164','165'])).

thf('167',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['103','166'])).

thf('168',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('169',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_B )
      = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('172',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('173',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('175',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('177',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( k2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['173','179'])).

thf('181',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( k2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('184',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['170','171','172','182','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('186',plain,
    ( ( ( m1_subset_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) ) ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v2_funct_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('188',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('189',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('190',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['188','191'])).

thf('193',plain,
    ( ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('194',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('195',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,
    ( ( v2_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('197',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('198',plain,
    ( ( v2_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['186','187','192','195','198'])).

thf('200',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('201',plain,
    ( ( r1_tarski @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['110','164','165'])).

thf('203',plain,(
    r1_tarski @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['201','202'])).

thf('204',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['170','171','172','182','183'])).

thf('205',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('207',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('208',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X14 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['206','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['205','210'])).

thf('212',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('213',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('215',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ k1_xboole_0 ) )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
        | ( X0
          = ( k2_relat_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['204','215'])).

thf('217',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['170','171','172','182','183'])).

thf('218',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
        | ( X0 = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['110','164','165'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simpl_trail,[status(thm)],['218','219'])).

thf('221',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['203','220'])).

thf('222',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['167','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('224',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('225',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['223','226'])).

thf('228',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('229',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('231',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('232',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('233',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('235',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['233','235'])).

thf('237',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['230','236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_relat_1 @ k1_xboole_0 ) )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['229','237'])).

thf('239',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['203','220'])).

thf('240',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('241',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['239','240'])).

thf('242',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['170','171','172','182','183'])).

thf('243',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['110','164','165'])).

thf('244',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['242','243'])).

thf('245',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['188','191'])).

thf('246',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('247',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['110','164','165'])).

thf('248',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['246','247'])).

thf('249',plain,
    ( ( v2_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('250',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['110','164','165'])).

thf('251',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['249','250'])).

thf('252',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['241','244','245','248','251'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['238','252'])).

thf('254',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['253'])).

thf('255',plain,(
    $false ),
    inference(demod,[status(thm)],['222','254'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.M4eGpKC9Pk
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:45:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.97/2.19  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.97/2.19  % Solved by: fo/fo7.sh
% 1.97/2.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.97/2.19  % done 2395 iterations in 1.744s
% 1.97/2.19  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.97/2.19  % SZS output start Refutation
% 1.97/2.19  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.97/2.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.97/2.19  thf(sk_B_type, type, sk_B: $i).
% 1.97/2.19  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.97/2.19  thf(sk_C_type, type, sk_C: $i).
% 1.97/2.19  thf(sk_A_type, type, sk_A: $i).
% 1.97/2.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.97/2.19  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.97/2.19  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.97/2.19  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.97/2.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.97/2.19  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.97/2.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.97/2.19  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.97/2.19  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.97/2.19  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.97/2.19  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.97/2.19  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.97/2.19  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.97/2.19  thf(t31_funct_2, conjecture,
% 1.97/2.19    (![A:$i,B:$i,C:$i]:
% 1.97/2.19     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.97/2.19         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.97/2.19       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.97/2.19         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.97/2.19           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.97/2.19           ( m1_subset_1 @
% 1.97/2.19             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.97/2.19  thf(zf_stmt_0, negated_conjecture,
% 1.97/2.19    (~( ![A:$i,B:$i,C:$i]:
% 1.97/2.19        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.97/2.19            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.97/2.19          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.97/2.19            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.97/2.19              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.97/2.19              ( m1_subset_1 @
% 1.97/2.19                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 1.97/2.19    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 1.97/2.19  thf('0', plain,
% 1.97/2.19      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.19        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 1.97/2.19        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.19             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('1', plain,
% 1.97/2.19      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.97/2.19         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.19      inference('split', [status(esa)], ['0'])).
% 1.97/2.19  thf(d1_funct_2, axiom,
% 1.97/2.19    (![A:$i,B:$i,C:$i]:
% 1.97/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.19       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.97/2.19           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.97/2.19             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.97/2.19         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.97/2.19           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.97/2.19             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.97/2.19  thf(zf_stmt_1, axiom,
% 1.97/2.19    (![B:$i,A:$i]:
% 1.97/2.19     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.97/2.19       ( zip_tseitin_0 @ B @ A ) ))).
% 1.97/2.19  thf('2', plain,
% 1.97/2.19      (![X23 : $i, X24 : $i]:
% 1.97/2.19         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.97/2.19  thf(t113_zfmisc_1, axiom,
% 1.97/2.19    (![A:$i,B:$i]:
% 1.97/2.19     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.97/2.19       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.97/2.19  thf('3', plain,
% 1.97/2.19      (![X4 : $i, X5 : $i]:
% 1.97/2.19         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 1.97/2.19      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.97/2.19  thf('4', plain,
% 1.97/2.19      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.97/2.19      inference('simplify', [status(thm)], ['3'])).
% 1.97/2.19  thf('5', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.19         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.97/2.19      inference('sup+', [status(thm)], ['2', '4'])).
% 1.97/2.19  thf('6', plain,
% 1.97/2.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.97/2.19  thf(zf_stmt_3, axiom,
% 1.97/2.19    (![C:$i,B:$i,A:$i]:
% 1.97/2.19     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.97/2.19       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.97/2.19  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.97/2.19  thf(zf_stmt_5, axiom,
% 1.97/2.19    (![A:$i,B:$i,C:$i]:
% 1.97/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.19       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.97/2.19         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.97/2.19           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.97/2.19             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.97/2.19  thf('7', plain,
% 1.97/2.19      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.97/2.19         (~ (zip_tseitin_0 @ X28 @ X29)
% 1.97/2.19          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 1.97/2.19          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.97/2.19  thf('8', plain,
% 1.97/2.19      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['6', '7'])).
% 1.97/2.19  thf('9', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 1.97/2.19          | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['5', '8'])).
% 1.97/2.19  thf('10', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('11', plain,
% 1.97/2.19      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.97/2.19         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 1.97/2.19          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 1.97/2.19          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.97/2.19  thf('12', plain,
% 1.97/2.19      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 1.97/2.19        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['10', '11'])).
% 1.97/2.19  thf('13', plain,
% 1.97/2.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf(redefinition_k1_relset_1, axiom,
% 1.97/2.19    (![A:$i,B:$i,C:$i]:
% 1.97/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.19       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.97/2.19  thf('14', plain,
% 1.97/2.19      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.97/2.19         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 1.97/2.19          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.97/2.19      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.97/2.19  thf('15', plain,
% 1.97/2.19      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.97/2.19      inference('sup-', [status(thm)], ['13', '14'])).
% 1.97/2.19  thf('16', plain,
% 1.97/2.19      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.97/2.19      inference('demod', [status(thm)], ['12', '15'])).
% 1.97/2.19  thf('17', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 1.97/2.19          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['9', '16'])).
% 1.97/2.19  thf('18', plain,
% 1.97/2.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('19', plain,
% 1.97/2.19      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.97/2.19        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.97/2.19      inference('sup+', [status(thm)], ['17', '18'])).
% 1.97/2.19  thf('20', plain,
% 1.97/2.19      (![X4 : $i, X5 : $i]:
% 1.97/2.19         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 1.97/2.19      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.97/2.19  thf('21', plain,
% 1.97/2.19      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 1.97/2.19      inference('simplify', [status(thm)], ['20'])).
% 1.97/2.19  thf(redefinition_k2_relset_1, axiom,
% 1.97/2.19    (![A:$i,B:$i,C:$i]:
% 1.97/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.19       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.97/2.19  thf('22', plain,
% 1.97/2.19      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.97/2.19         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 1.97/2.19          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.97/2.19      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.97/2.19  thf('23', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i]:
% 1.97/2.19         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.97/2.19          | ((k2_relset_1 @ k1_xboole_0 @ X0 @ X1) = (k2_relat_1 @ X1)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['21', '22'])).
% 1.97/2.19  thf('24', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (((sk_A) = (k1_relat_1 @ sk_C))
% 1.97/2.19          | ((k2_relset_1 @ k1_xboole_0 @ X0 @ sk_C) = (k2_relat_1 @ sk_C)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['19', '23'])).
% 1.97/2.19  thf('25', plain,
% 1.97/2.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('26', plain,
% 1.97/2.19      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.97/2.19         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 1.97/2.19          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.97/2.19      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.97/2.19  thf('27', plain,
% 1.97/2.19      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.97/2.19      inference('sup-', [status(thm)], ['25', '26'])).
% 1.97/2.19  thf('28', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('29', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.97/2.19      inference('sup+', [status(thm)], ['27', '28'])).
% 1.97/2.19  thf('30', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (((sk_A) = (k1_relat_1 @ sk_C))
% 1.97/2.19          | ((k2_relset_1 @ k1_xboole_0 @ X0 @ sk_C) = (sk_B)))),
% 1.97/2.19      inference('demod', [status(thm)], ['24', '29'])).
% 1.97/2.19  thf('31', plain,
% 1.97/2.19      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.97/2.19        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.97/2.19      inference('sup+', [status(thm)], ['17', '18'])).
% 1.97/2.19  thf('32', plain,
% 1.97/2.19      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 1.97/2.19      inference('simplify', [status(thm)], ['20'])).
% 1.97/2.19  thf(dt_k2_relset_1, axiom,
% 1.97/2.19    (![A:$i,B:$i,C:$i]:
% 1.97/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.19       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.97/2.19  thf('33', plain,
% 1.97/2.19      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.97/2.19         ((m1_subset_1 @ (k2_relset_1 @ X14 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))
% 1.97/2.19          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.97/2.19      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 1.97/2.19  thf('34', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i]:
% 1.97/2.19         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.97/2.19          | (m1_subset_1 @ (k2_relset_1 @ k1_xboole_0 @ X0 @ X1) @ 
% 1.97/2.19             (k1_zfmisc_1 @ X0)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['32', '33'])).
% 1.97/2.19  thf('35', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (((sk_A) = (k1_relat_1 @ sk_C))
% 1.97/2.19          | (m1_subset_1 @ (k2_relset_1 @ k1_xboole_0 @ X0 @ sk_C) @ 
% 1.97/2.19             (k1_zfmisc_1 @ X0)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['31', '34'])).
% 1.97/2.19  thf('36', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ X0))
% 1.97/2.19          | ((sk_A) = (k1_relat_1 @ sk_C))
% 1.97/2.19          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.97/2.19      inference('sup+', [status(thm)], ['30', '35'])).
% 1.97/2.19  thf('37', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (((sk_A) = (k1_relat_1 @ sk_C))
% 1.97/2.19          | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ X0)))),
% 1.97/2.19      inference('simplify', [status(thm)], ['36'])).
% 1.97/2.19  thf(t3_subset, axiom,
% 1.97/2.19    (![A:$i,B:$i]:
% 1.97/2.19     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.97/2.19  thf('38', plain,
% 1.97/2.19      (![X6 : $i, X7 : $i]:
% 1.97/2.19         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 1.97/2.19      inference('cnf', [status(esa)], [t3_subset])).
% 1.97/2.19  thf('39', plain,
% 1.97/2.19      (![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_C)) | (r1_tarski @ sk_B @ X0))),
% 1.97/2.19      inference('sup-', [status(thm)], ['37', '38'])).
% 1.97/2.19  thf('40', plain,
% 1.97/2.19      (![X23 : $i, X24 : $i]:
% 1.97/2.19         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.97/2.19  thf('41', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.19         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.97/2.19      inference('sup+', [status(thm)], ['2', '4'])).
% 1.97/2.19  thf('42', plain,
% 1.97/2.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('43', plain,
% 1.97/2.19      (![X6 : $i, X7 : $i]:
% 1.97/2.19         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 1.97/2.19      inference('cnf', [status(esa)], [t3_subset])).
% 1.97/2.19  thf('44', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 1.97/2.19      inference('sup-', [status(thm)], ['42', '43'])).
% 1.97/2.19  thf('45', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         ((r1_tarski @ sk_C @ k1_xboole_0) | (zip_tseitin_0 @ sk_B @ X0))),
% 1.97/2.19      inference('sup+', [status(thm)], ['41', '44'])).
% 1.97/2.19  thf('46', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.19         ((r1_tarski @ sk_C @ X0)
% 1.97/2.19          | (zip_tseitin_0 @ X0 @ X2)
% 1.97/2.19          | (zip_tseitin_0 @ sk_B @ X1))),
% 1.97/2.19      inference('sup+', [status(thm)], ['40', '45'])).
% 1.97/2.19  thf('47', plain,
% 1.97/2.19      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (r1_tarski @ sk_C @ sk_B))),
% 1.97/2.19      inference('eq_fact', [status(thm)], ['46'])).
% 1.97/2.19  thf(d10_xboole_0, axiom,
% 1.97/2.19    (![A:$i,B:$i]:
% 1.97/2.19     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.97/2.19  thf('48', plain,
% 1.97/2.19      (![X0 : $i, X2 : $i]:
% 1.97/2.19         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.97/2.19      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.97/2.19  thf('49', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         ((zip_tseitin_0 @ sk_B @ X0)
% 1.97/2.19          | ~ (r1_tarski @ sk_B @ sk_C)
% 1.97/2.19          | ((sk_B) = (sk_C)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['47', '48'])).
% 1.97/2.19  thf('50', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (((sk_A) = (k1_relat_1 @ sk_C))
% 1.97/2.19          | ((sk_B) = (sk_C))
% 1.97/2.19          | (zip_tseitin_0 @ sk_B @ X0))),
% 1.97/2.19      inference('sup-', [status(thm)], ['39', '49'])).
% 1.97/2.19  thf('51', plain,
% 1.97/2.19      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['6', '7'])).
% 1.97/2.19  thf('52', plain,
% 1.97/2.19      ((((sk_B) = (sk_C))
% 1.97/2.19        | ((sk_A) = (k1_relat_1 @ sk_C))
% 1.97/2.19        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['50', '51'])).
% 1.97/2.19  thf('53', plain,
% 1.97/2.19      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.97/2.19      inference('demod', [status(thm)], ['12', '15'])).
% 1.97/2.19  thf('54', plain, ((((sk_A) = (k1_relat_1 @ sk_C)) | ((sk_B) = (sk_C)))),
% 1.97/2.19      inference('clc', [status(thm)], ['52', '53'])).
% 1.97/2.19  thf(t55_funct_1, axiom,
% 1.97/2.19    (![A:$i]:
% 1.97/2.19     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.97/2.19       ( ( v2_funct_1 @ A ) =>
% 1.97/2.19         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.97/2.19           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.97/2.19  thf('55', plain,
% 1.97/2.19      (![X10 : $i]:
% 1.97/2.19         (~ (v2_funct_1 @ X10)
% 1.97/2.19          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 1.97/2.19          | ~ (v1_funct_1 @ X10)
% 1.97/2.19          | ~ (v1_relat_1 @ X10))),
% 1.97/2.19      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.97/2.19  thf(dt_k2_funct_1, axiom,
% 1.97/2.19    (![A:$i]:
% 1.97/2.19     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.97/2.19       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.97/2.19         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.97/2.19  thf('56', plain,
% 1.97/2.19      (![X9 : $i]:
% 1.97/2.19         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 1.97/2.19          | ~ (v1_funct_1 @ X9)
% 1.97/2.19          | ~ (v1_relat_1 @ X9))),
% 1.97/2.19      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.97/2.19  thf('57', plain,
% 1.97/2.19      (![X9 : $i]:
% 1.97/2.19         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.97/2.19          | ~ (v1_funct_1 @ X9)
% 1.97/2.19          | ~ (v1_relat_1 @ X9))),
% 1.97/2.19      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.97/2.19  thf('58', plain,
% 1.97/2.19      (![X10 : $i]:
% 1.97/2.19         (~ (v2_funct_1 @ X10)
% 1.97/2.19          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 1.97/2.19          | ~ (v1_funct_1 @ X10)
% 1.97/2.19          | ~ (v1_relat_1 @ X10))),
% 1.97/2.19      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.97/2.19  thf(t3_funct_2, axiom,
% 1.97/2.19    (![A:$i]:
% 1.97/2.19     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.97/2.19       ( ( v1_funct_1 @ A ) & 
% 1.97/2.19         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.97/2.19         ( m1_subset_1 @
% 1.97/2.19           A @ 
% 1.97/2.19           ( k1_zfmisc_1 @
% 1.97/2.19             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.97/2.19  thf('59', plain,
% 1.97/2.19      (![X31 : $i]:
% 1.97/2.19         ((v1_funct_2 @ X31 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))
% 1.97/2.19          | ~ (v1_funct_1 @ X31)
% 1.97/2.19          | ~ (v1_relat_1 @ X31))),
% 1.97/2.19      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.97/2.19  thf('60', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.97/2.19           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.97/2.19          | ~ (v1_relat_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v2_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.19          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.97/2.19      inference('sup+', [status(thm)], ['58', '59'])).
% 1.97/2.19  thf('61', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (~ (v1_relat_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.19          | ~ (v2_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_relat_1 @ X0)
% 1.97/2.19          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.97/2.19             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.97/2.19      inference('sup-', [status(thm)], ['57', '60'])).
% 1.97/2.19  thf('62', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.97/2.19           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.97/2.19          | ~ (v2_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_relat_1 @ X0))),
% 1.97/2.19      inference('simplify', [status(thm)], ['61'])).
% 1.97/2.19  thf('63', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (~ (v1_relat_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_relat_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v2_funct_1 @ X0)
% 1.97/2.19          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.97/2.19             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.97/2.19      inference('sup-', [status(thm)], ['56', '62'])).
% 1.97/2.19  thf('64', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.97/2.19           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.97/2.19          | ~ (v2_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_relat_1 @ X0))),
% 1.97/2.19      inference('simplify', [status(thm)], ['63'])).
% 1.97/2.19  thf('65', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.97/2.19           (k1_relat_1 @ X0))
% 1.97/2.19          | ~ (v1_relat_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v2_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_relat_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v2_funct_1 @ X0))),
% 1.97/2.19      inference('sup+', [status(thm)], ['55', '64'])).
% 1.97/2.19  thf('66', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (~ (v2_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_relat_1 @ X0)
% 1.97/2.19          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.97/2.19             (k1_relat_1 @ X0)))),
% 1.97/2.19      inference('simplify', [status(thm)], ['65'])).
% 1.97/2.19  thf('67', plain,
% 1.97/2.19      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 1.97/2.19        | ((sk_B) = (sk_C))
% 1.97/2.19        | ~ (v1_relat_1 @ sk_C)
% 1.97/2.19        | ~ (v1_funct_1 @ sk_C)
% 1.97/2.19        | ~ (v2_funct_1 @ sk_C))),
% 1.97/2.19      inference('sup+', [status(thm)], ['54', '66'])).
% 1.97/2.19  thf('68', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.97/2.19      inference('sup+', [status(thm)], ['27', '28'])).
% 1.97/2.19  thf('69', plain,
% 1.97/2.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf(cc1_relset_1, axiom,
% 1.97/2.19    (![A:$i,B:$i,C:$i]:
% 1.97/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.19       ( v1_relat_1 @ C ) ))).
% 1.97/2.19  thf('70', plain,
% 1.97/2.19      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.97/2.19         ((v1_relat_1 @ X11)
% 1.97/2.19          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.97/2.19      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.97/2.19  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.19      inference('sup-', [status(thm)], ['69', '70'])).
% 1.97/2.19  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('73', plain, ((v2_funct_1 @ sk_C)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('74', plain,
% 1.97/2.19      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A) | ((sk_B) = (sk_C)))),
% 1.97/2.19      inference('demod', [status(thm)], ['67', '68', '71', '72', '73'])).
% 1.97/2.19  thf('75', plain,
% 1.97/2.19      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.97/2.19         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.19      inference('split', [status(esa)], ['0'])).
% 1.97/2.19  thf('76', plain,
% 1.97/2.19      ((((sk_B) = (sk_C)))
% 1.97/2.19         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['74', '75'])).
% 1.97/2.19  thf('77', plain,
% 1.97/2.19      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A))
% 1.97/2.19         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.19      inference('demod', [status(thm)], ['1', '76'])).
% 1.97/2.19  thf('78', plain,
% 1.97/2.19      ((((sk_B) = (sk_C)))
% 1.97/2.19         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['74', '75'])).
% 1.97/2.19  thf('79', plain,
% 1.97/2.19      (![X23 : $i, X24 : $i]:
% 1.97/2.19         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.97/2.19  thf('80', plain,
% 1.97/2.19      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['6', '7'])).
% 1.97/2.19  thf('81', plain,
% 1.97/2.19      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['79', '80'])).
% 1.97/2.19  thf('82', plain,
% 1.97/2.19      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.97/2.19      inference('demod', [status(thm)], ['12', '15'])).
% 1.97/2.19  thf('83', plain,
% 1.97/2.19      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['81', '82'])).
% 1.97/2.19  thf('84', plain,
% 1.97/2.19      (((((sk_A) = (k1_relat_1 @ sk_B)) | ((sk_B) = (k1_xboole_0))))
% 1.97/2.19         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.19      inference('sup+', [status(thm)], ['78', '83'])).
% 1.97/2.19  thf('85', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (~ (v2_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_relat_1 @ X0)
% 1.97/2.19          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.97/2.19             (k1_relat_1 @ X0)))),
% 1.97/2.19      inference('simplify', [status(thm)], ['65'])).
% 1.97/2.19  thf('86', plain,
% 1.97/2.19      ((((v1_funct_2 @ (k2_funct_1 @ sk_B) @ (k2_relat_1 @ sk_B) @ sk_A)
% 1.97/2.19         | ((sk_B) = (k1_xboole_0))
% 1.97/2.19         | ~ (v1_relat_1 @ sk_B)
% 1.97/2.19         | ~ (v1_funct_1 @ sk_B)
% 1.97/2.19         | ~ (v2_funct_1 @ sk_B)))
% 1.97/2.19         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.19      inference('sup+', [status(thm)], ['84', '85'])).
% 1.97/2.19  thf('87', plain,
% 1.97/2.19      ((((sk_B) = (sk_C)))
% 1.97/2.19         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['74', '75'])).
% 1.97/2.19  thf('88', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.97/2.19      inference('sup+', [status(thm)], ['27', '28'])).
% 1.97/2.19  thf('89', plain,
% 1.97/2.19      ((((k2_relat_1 @ sk_B) = (sk_B)))
% 1.97/2.19         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.19      inference('sup+', [status(thm)], ['87', '88'])).
% 1.97/2.19  thf('90', plain,
% 1.97/2.19      ((((sk_B) = (sk_C)))
% 1.97/2.19         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['74', '75'])).
% 1.97/2.19  thf('91', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.19      inference('sup-', [status(thm)], ['69', '70'])).
% 1.97/2.19  thf('92', plain,
% 1.97/2.19      (((v1_relat_1 @ sk_B))
% 1.97/2.19         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.19      inference('sup+', [status(thm)], ['90', '91'])).
% 1.97/2.19  thf('93', plain,
% 1.97/2.19      ((((sk_B) = (sk_C)))
% 1.97/2.19         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['74', '75'])).
% 1.97/2.19  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('95', plain,
% 1.97/2.19      (((v1_funct_1 @ sk_B))
% 1.97/2.19         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.19      inference('sup+', [status(thm)], ['93', '94'])).
% 1.97/2.19  thf('96', plain,
% 1.97/2.19      ((((sk_B) = (sk_C)))
% 1.97/2.19         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['74', '75'])).
% 1.97/2.19  thf('97', plain, ((v2_funct_1 @ sk_C)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('98', plain,
% 1.97/2.19      (((v2_funct_1 @ sk_B))
% 1.97/2.19         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.19      inference('sup+', [status(thm)], ['96', '97'])).
% 1.97/2.19  thf('99', plain,
% 1.97/2.19      ((((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A)
% 1.97/2.19         | ((sk_B) = (k1_xboole_0))))
% 1.97/2.19         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.19      inference('demod', [status(thm)], ['86', '89', '92', '95', '98'])).
% 1.97/2.19  thf('100', plain,
% 1.97/2.19      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A))
% 1.97/2.19         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.19      inference('demod', [status(thm)], ['1', '76'])).
% 1.97/2.19  thf('101', plain,
% 1.97/2.19      ((((sk_B) = (k1_xboole_0)))
% 1.97/2.19         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.19      inference('clc', [status(thm)], ['99', '100'])).
% 1.97/2.19  thf('102', plain,
% 1.97/2.19      ((((sk_B) = (k1_xboole_0)))
% 1.97/2.19         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.19      inference('clc', [status(thm)], ['99', '100'])).
% 1.97/2.19  thf('103', plain,
% 1.97/2.19      ((~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A))
% 1.97/2.19         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.19      inference('demod', [status(thm)], ['77', '101', '102'])).
% 1.97/2.19  thf('104', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.19      inference('sup-', [status(thm)], ['69', '70'])).
% 1.97/2.19  thf('105', plain,
% 1.97/2.19      (![X9 : $i]:
% 1.97/2.19         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 1.97/2.19          | ~ (v1_funct_1 @ X9)
% 1.97/2.19          | ~ (v1_relat_1 @ X9))),
% 1.97/2.19      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.97/2.19  thf('106', plain,
% 1.97/2.19      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.97/2.19         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.97/2.19      inference('split', [status(esa)], ['0'])).
% 1.97/2.19  thf('107', plain,
% 1.97/2.19      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 1.97/2.19         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.97/2.19      inference('sup-', [status(thm)], ['105', '106'])).
% 1.97/2.19  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('109', plain,
% 1.97/2.19      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.97/2.19      inference('demod', [status(thm)], ['107', '108'])).
% 1.97/2.19  thf('110', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['104', '109'])).
% 1.97/2.19  thf('111', plain,
% 1.97/2.19      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.19           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.97/2.19         <= (~
% 1.97/2.19             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.19               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.97/2.19      inference('split', [status(esa)], ['0'])).
% 1.97/2.19  thf('112', plain,
% 1.97/2.19      (![X10 : $i]:
% 1.97/2.19         (~ (v2_funct_1 @ X10)
% 1.97/2.19          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 1.97/2.19          | ~ (v1_funct_1 @ X10)
% 1.97/2.19          | ~ (v1_relat_1 @ X10))),
% 1.97/2.19      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.97/2.19  thf('113', plain,
% 1.97/2.19      (![X9 : $i]:
% 1.97/2.19         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.97/2.19          | ~ (v1_funct_1 @ X9)
% 1.97/2.19          | ~ (v1_relat_1 @ X9))),
% 1.97/2.19      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.97/2.19  thf('114', plain,
% 1.97/2.19      (![X9 : $i]:
% 1.97/2.19         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 1.97/2.19          | ~ (v1_funct_1 @ X9)
% 1.97/2.19          | ~ (v1_relat_1 @ X9))),
% 1.97/2.19      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.97/2.19  thf('115', plain,
% 1.97/2.19      (![X23 : $i, X24 : $i]:
% 1.97/2.19         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.97/2.19  thf('116', plain,
% 1.97/2.19      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 1.97/2.19      inference('simplify', [status(thm)], ['20'])).
% 1.97/2.19  thf('117', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.19         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.97/2.19      inference('sup+', [status(thm)], ['115', '116'])).
% 1.97/2.19  thf('118', plain,
% 1.97/2.19      (![X31 : $i]:
% 1.97/2.19         ((m1_subset_1 @ X31 @ 
% 1.97/2.19           (k1_zfmisc_1 @ 
% 1.97/2.19            (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))))
% 1.97/2.19          | ~ (v1_funct_1 @ X31)
% 1.97/2.19          | ~ (v1_relat_1 @ X31))),
% 1.97/2.19      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.97/2.19  thf('119', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i]:
% 1.97/2.19         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.97/2.19          | (zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 1.97/2.19          | ~ (v1_relat_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ X0))),
% 1.97/2.19      inference('sup+', [status(thm)], ['117', '118'])).
% 1.97/2.19  thf('120', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.19         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.97/2.19      inference('sup+', [status(thm)], ['115', '116'])).
% 1.97/2.19  thf('121', plain,
% 1.97/2.19      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['6', '7'])).
% 1.97/2.19  thf('122', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 1.97/2.19          | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['120', '121'])).
% 1.97/2.19  thf('123', plain,
% 1.97/2.19      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.97/2.19      inference('demod', [status(thm)], ['12', '15'])).
% 1.97/2.19  thf('124', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 1.97/2.19          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['122', '123'])).
% 1.97/2.19  thf('125', plain,
% 1.97/2.19      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.19           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.97/2.19         <= (~
% 1.97/2.19             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.19               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.97/2.19      inference('split', [status(esa)], ['0'])).
% 1.97/2.19  thf('126', plain,
% 1.97/2.19      (((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.97/2.19         | ((sk_A) = (k1_relat_1 @ sk_C))))
% 1.97/2.19         <= (~
% 1.97/2.19             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.19               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.97/2.19      inference('sup-', [status(thm)], ['124', '125'])).
% 1.97/2.19  thf('127', plain,
% 1.97/2.19      ((![X0 : $i]:
% 1.97/2.19          (~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.19           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.19           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 1.97/2.19           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 1.97/2.19         <= (~
% 1.97/2.19             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.19               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.97/2.19      inference('sup-', [status(thm)], ['119', '126'])).
% 1.97/2.19  thf('128', plain,
% 1.97/2.19      ((![X0 : $i]:
% 1.97/2.19          (~ (v1_relat_1 @ sk_C)
% 1.97/2.19           | ~ (v1_funct_1 @ sk_C)
% 1.97/2.19           | ((sk_A) = (k1_relat_1 @ sk_C))
% 1.97/2.19           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 1.97/2.19           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.97/2.19         <= (~
% 1.97/2.19             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.19               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.97/2.19      inference('sup-', [status(thm)], ['114', '127'])).
% 1.97/2.19  thf('129', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.19      inference('sup-', [status(thm)], ['69', '70'])).
% 1.97/2.19  thf('130', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('131', plain,
% 1.97/2.19      ((![X0 : $i]:
% 1.97/2.19          (((sk_A) = (k1_relat_1 @ sk_C))
% 1.97/2.19           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 1.97/2.19           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.97/2.19         <= (~
% 1.97/2.19             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.19               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.97/2.19      inference('demod', [status(thm)], ['128', '129', '130'])).
% 1.97/2.19  thf('132', plain,
% 1.97/2.19      ((![X0 : $i]:
% 1.97/2.19          (~ (v1_relat_1 @ sk_C)
% 1.97/2.19           | ~ (v1_funct_1 @ sk_C)
% 1.97/2.19           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 1.97/2.19           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 1.97/2.19         <= (~
% 1.97/2.19             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.19               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.97/2.19      inference('sup-', [status(thm)], ['113', '131'])).
% 1.97/2.19  thf('133', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.19      inference('sup-', [status(thm)], ['69', '70'])).
% 1.97/2.19  thf('134', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('135', plain,
% 1.97/2.19      ((![X0 : $i]:
% 1.97/2.19          ((zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 1.97/2.19           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 1.97/2.19         <= (~
% 1.97/2.19             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.19               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.97/2.19      inference('demod', [status(thm)], ['132', '133', '134'])).
% 1.97/2.19  thf('136', plain,
% 1.97/2.19      ((![X0 : $i]:
% 1.97/2.19          ((zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ X0)
% 1.97/2.19           | ~ (v1_relat_1 @ sk_C)
% 1.97/2.19           | ~ (v1_funct_1 @ sk_C)
% 1.97/2.19           | ~ (v2_funct_1 @ sk_C)
% 1.97/2.19           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 1.97/2.19         <= (~
% 1.97/2.19             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.19               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.97/2.19      inference('sup+', [status(thm)], ['112', '135'])).
% 1.97/2.19  thf('137', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.97/2.19      inference('sup+', [status(thm)], ['27', '28'])).
% 1.97/2.19  thf('138', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.19      inference('sup-', [status(thm)], ['69', '70'])).
% 1.97/2.19  thf('139', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('140', plain, ((v2_funct_1 @ sk_C)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('141', plain,
% 1.97/2.19      ((![X0 : $i]:
% 1.97/2.19          ((zip_tseitin_0 @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_C))))
% 1.97/2.19         <= (~
% 1.97/2.19             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.19               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.97/2.19      inference('demod', [status(thm)], ['136', '137', '138', '139', '140'])).
% 1.97/2.19  thf('142', plain,
% 1.97/2.19      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['6', '7'])).
% 1.97/2.19  thf('143', plain,
% 1.97/2.19      (((((sk_A) = (k1_relat_1 @ sk_C)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)))
% 1.97/2.19         <= (~
% 1.97/2.19             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.19               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.97/2.19      inference('sup-', [status(thm)], ['141', '142'])).
% 1.97/2.19  thf('144', plain,
% 1.97/2.19      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.97/2.19      inference('demod', [status(thm)], ['12', '15'])).
% 1.97/2.19  thf('145', plain,
% 1.97/2.19      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 1.97/2.19         <= (~
% 1.97/2.19             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.19               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.97/2.19      inference('clc', [status(thm)], ['143', '144'])).
% 1.97/2.19  thf('146', plain,
% 1.97/2.19      (![X10 : $i]:
% 1.97/2.19         (~ (v2_funct_1 @ X10)
% 1.97/2.19          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 1.97/2.19          | ~ (v1_funct_1 @ X10)
% 1.97/2.19          | ~ (v1_relat_1 @ X10))),
% 1.97/2.19      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.97/2.19  thf('147', plain,
% 1.97/2.19      (![X9 : $i]:
% 1.97/2.19         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 1.97/2.19          | ~ (v1_funct_1 @ X9)
% 1.97/2.19          | ~ (v1_relat_1 @ X9))),
% 1.97/2.19      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.97/2.19  thf('148', plain,
% 1.97/2.19      (![X9 : $i]:
% 1.97/2.19         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.97/2.19          | ~ (v1_funct_1 @ X9)
% 1.97/2.19          | ~ (v1_relat_1 @ X9))),
% 1.97/2.19      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.97/2.19  thf('149', plain,
% 1.97/2.19      (![X10 : $i]:
% 1.97/2.19         (~ (v2_funct_1 @ X10)
% 1.97/2.19          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 1.97/2.19          | ~ (v1_funct_1 @ X10)
% 1.97/2.19          | ~ (v1_relat_1 @ X10))),
% 1.97/2.19      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.97/2.19  thf('150', plain,
% 1.97/2.19      (![X31 : $i]:
% 1.97/2.19         ((m1_subset_1 @ X31 @ 
% 1.97/2.19           (k1_zfmisc_1 @ 
% 1.97/2.19            (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))))
% 1.97/2.19          | ~ (v1_funct_1 @ X31)
% 1.97/2.19          | ~ (v1_relat_1 @ X31))),
% 1.97/2.19      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.97/2.19  thf('151', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.97/2.19           (k1_zfmisc_1 @ 
% 1.97/2.19            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.97/2.19          | ~ (v1_relat_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v2_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.19          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.97/2.19      inference('sup+', [status(thm)], ['149', '150'])).
% 1.97/2.19  thf('152', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (~ (v1_relat_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.19          | ~ (v2_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_relat_1 @ X0)
% 1.97/2.19          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.97/2.19             (k1_zfmisc_1 @ 
% 1.97/2.19              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.97/2.19               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.97/2.19      inference('sup-', [status(thm)], ['148', '151'])).
% 1.97/2.19  thf('153', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.97/2.19           (k1_zfmisc_1 @ 
% 1.97/2.19            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.97/2.19          | ~ (v2_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_relat_1 @ X0))),
% 1.97/2.19      inference('simplify', [status(thm)], ['152'])).
% 1.97/2.19  thf('154', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (~ (v1_relat_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_relat_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v2_funct_1 @ X0)
% 1.97/2.19          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.97/2.19             (k1_zfmisc_1 @ 
% 1.97/2.19              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.97/2.19               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.97/2.19      inference('sup-', [status(thm)], ['147', '153'])).
% 1.97/2.19  thf('155', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.97/2.19           (k1_zfmisc_1 @ 
% 1.97/2.19            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.97/2.19          | ~ (v2_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_relat_1 @ X0))),
% 1.97/2.19      inference('simplify', [status(thm)], ['154'])).
% 1.97/2.19  thf('156', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.97/2.19           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 1.97/2.19          | ~ (v1_relat_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v2_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_relat_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v2_funct_1 @ X0))),
% 1.97/2.19      inference('sup+', [status(thm)], ['146', '155'])).
% 1.97/2.19  thf('157', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (~ (v2_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_funct_1 @ X0)
% 1.97/2.19          | ~ (v1_relat_1 @ X0)
% 1.97/2.19          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.97/2.19             (k1_zfmisc_1 @ 
% 1.97/2.19              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 1.97/2.19      inference('simplify', [status(thm)], ['156'])).
% 1.97/2.19  thf('158', plain,
% 1.97/2.19      ((((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.19          (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 1.97/2.19         | ~ (v1_relat_1 @ sk_C)
% 1.97/2.19         | ~ (v1_funct_1 @ sk_C)
% 1.97/2.19         | ~ (v2_funct_1 @ sk_C)))
% 1.97/2.19         <= (~
% 1.97/2.19             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.19               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.97/2.19      inference('sup+', [status(thm)], ['145', '157'])).
% 1.97/2.19  thf('159', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.97/2.19      inference('sup+', [status(thm)], ['27', '28'])).
% 1.97/2.20  thf('160', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.20      inference('sup-', [status(thm)], ['69', '70'])).
% 1.97/2.20  thf('161', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.20  thf('162', plain, ((v2_funct_1 @ sk_C)),
% 1.97/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.20  thf('163', plain,
% 1.97/2.20      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.20         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.97/2.20         <= (~
% 1.97/2.20             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.20               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.97/2.20      inference('demod', [status(thm)], ['158', '159', '160', '161', '162'])).
% 1.97/2.20  thf('164', plain,
% 1.97/2.20      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.20         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.97/2.20      inference('demod', [status(thm)], ['111', '163'])).
% 1.97/2.20  thf('165', plain,
% 1.97/2.20      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 1.97/2.20       ~
% 1.97/2.20       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.20         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 1.97/2.20       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.97/2.20      inference('split', [status(esa)], ['0'])).
% 1.97/2.20  thf('166', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 1.97/2.20      inference('sat_resolution*', [status(thm)], ['110', '164', '165'])).
% 1.97/2.20  thf('167', plain,
% 1.97/2.20      (~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A)),
% 1.97/2.20      inference('simpl_trail', [status(thm)], ['103', '166'])).
% 1.97/2.20  thf('168', plain,
% 1.97/2.20      ((((sk_B) = (sk_C)))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('sup-', [status(thm)], ['74', '75'])).
% 1.97/2.20  thf('169', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.97/2.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.20  thf('170', plain,
% 1.97/2.20      ((((k2_relset_1 @ sk_A @ sk_B @ sk_B) = (sk_B)))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('sup+', [status(thm)], ['168', '169'])).
% 1.97/2.20  thf('171', plain,
% 1.97/2.20      ((((sk_B) = (k1_xboole_0)))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('clc', [status(thm)], ['99', '100'])).
% 1.97/2.20  thf('172', plain,
% 1.97/2.20      ((((sk_B) = (k1_xboole_0)))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('clc', [status(thm)], ['99', '100'])).
% 1.97/2.20  thf('173', plain,
% 1.97/2.20      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.97/2.20      inference('simplify', [status(thm)], ['3'])).
% 1.97/2.20  thf('174', plain,
% 1.97/2.20      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.97/2.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.97/2.20  thf('175', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.97/2.20      inference('simplify', [status(thm)], ['174'])).
% 1.97/2.20  thf('176', plain,
% 1.97/2.20      (![X6 : $i, X8 : $i]:
% 1.97/2.20         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 1.97/2.20      inference('cnf', [status(esa)], [t3_subset])).
% 1.97/2.20  thf('177', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.97/2.20      inference('sup-', [status(thm)], ['175', '176'])).
% 1.97/2.20  thf('178', plain,
% 1.97/2.20      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.97/2.20         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 1.97/2.20          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.97/2.20      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.97/2.20  thf('179', plain,
% 1.97/2.20      (![X0 : $i, X1 : $i]:
% 1.97/2.20         ((k2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.97/2.20           = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 1.97/2.20      inference('sup-', [status(thm)], ['177', '178'])).
% 1.97/2.20  thf('180', plain,
% 1.97/2.20      (![X0 : $i]:
% 1.97/2.20         ((k2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 1.97/2.20           = (k2_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)))),
% 1.97/2.20      inference('sup+', [status(thm)], ['173', '179'])).
% 1.97/2.20  thf('181', plain,
% 1.97/2.20      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.97/2.20      inference('simplify', [status(thm)], ['3'])).
% 1.97/2.20  thf('182', plain,
% 1.97/2.20      (![X0 : $i]:
% 1.97/2.20         ((k2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 1.97/2.20           = (k2_relat_1 @ k1_xboole_0))),
% 1.97/2.20      inference('demod', [status(thm)], ['180', '181'])).
% 1.97/2.20  thf('183', plain,
% 1.97/2.20      ((((sk_B) = (k1_xboole_0)))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('clc', [status(thm)], ['99', '100'])).
% 1.97/2.20  thf('184', plain,
% 1.97/2.20      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('demod', [status(thm)], ['170', '171', '172', '182', '183'])).
% 1.97/2.20  thf('185', plain,
% 1.97/2.20      (![X0 : $i]:
% 1.97/2.20         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.97/2.20           (k1_zfmisc_1 @ 
% 1.97/2.20            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.97/2.20          | ~ (v2_funct_1 @ X0)
% 1.97/2.20          | ~ (v1_funct_1 @ X0)
% 1.97/2.20          | ~ (v1_relat_1 @ X0))),
% 1.97/2.20      inference('simplify', [status(thm)], ['154'])).
% 1.97/2.20  thf('186', plain,
% 1.97/2.20      ((((m1_subset_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 1.97/2.20          (k1_zfmisc_1 @ 
% 1.97/2.20           (k2_zfmisc_1 @ k1_xboole_0 @ 
% 1.97/2.20            (k2_relat_1 @ (k2_funct_1 @ k1_xboole_0)))))
% 1.97/2.20         | ~ (v1_relat_1 @ k1_xboole_0)
% 1.97/2.20         | ~ (v1_funct_1 @ k1_xboole_0)
% 1.97/2.20         | ~ (v2_funct_1 @ k1_xboole_0)))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('sup+', [status(thm)], ['184', '185'])).
% 1.97/2.20  thf('187', plain,
% 1.97/2.20      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 1.97/2.20      inference('simplify', [status(thm)], ['20'])).
% 1.97/2.20  thf('188', plain,
% 1.97/2.20      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.97/2.20      inference('simplify', [status(thm)], ['3'])).
% 1.97/2.20  thf('189', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.97/2.20      inference('sup-', [status(thm)], ['175', '176'])).
% 1.97/2.20  thf('190', plain,
% 1.97/2.20      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.97/2.20         ((v1_relat_1 @ X11)
% 1.97/2.20          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.97/2.20      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.97/2.20  thf('191', plain,
% 1.97/2.20      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 1.97/2.20      inference('sup-', [status(thm)], ['189', '190'])).
% 1.97/2.20  thf('192', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.97/2.20      inference('sup+', [status(thm)], ['188', '191'])).
% 1.97/2.20  thf('193', plain,
% 1.97/2.20      (((v1_funct_1 @ sk_B))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('sup+', [status(thm)], ['93', '94'])).
% 1.97/2.20  thf('194', plain,
% 1.97/2.20      ((((sk_B) = (k1_xboole_0)))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('clc', [status(thm)], ['99', '100'])).
% 1.97/2.20  thf('195', plain,
% 1.97/2.20      (((v1_funct_1 @ k1_xboole_0))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('demod', [status(thm)], ['193', '194'])).
% 1.97/2.20  thf('196', plain,
% 1.97/2.20      (((v2_funct_1 @ sk_B))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('sup+', [status(thm)], ['96', '97'])).
% 1.97/2.20  thf('197', plain,
% 1.97/2.20      ((((sk_B) = (k1_xboole_0)))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('clc', [status(thm)], ['99', '100'])).
% 1.97/2.20  thf('198', plain,
% 1.97/2.20      (((v2_funct_1 @ k1_xboole_0))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('demod', [status(thm)], ['196', '197'])).
% 1.97/2.20  thf('199', plain,
% 1.97/2.20      (((m1_subset_1 @ (k2_funct_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('demod', [status(thm)], ['186', '187', '192', '195', '198'])).
% 1.97/2.20  thf('200', plain,
% 1.97/2.20      (![X6 : $i, X7 : $i]:
% 1.97/2.20         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 1.97/2.20      inference('cnf', [status(esa)], [t3_subset])).
% 1.97/2.20  thf('201', plain,
% 1.97/2.20      (((r1_tarski @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('sup-', [status(thm)], ['199', '200'])).
% 1.97/2.20  thf('202', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 1.97/2.20      inference('sat_resolution*', [status(thm)], ['110', '164', '165'])).
% 1.97/2.20  thf('203', plain, ((r1_tarski @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0)),
% 1.97/2.20      inference('simpl_trail', [status(thm)], ['201', '202'])).
% 1.97/2.20  thf('204', plain,
% 1.97/2.20      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('demod', [status(thm)], ['170', '171', '172', '182', '183'])).
% 1.97/2.20  thf('205', plain,
% 1.97/2.20      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 1.97/2.20      inference('simplify', [status(thm)], ['20'])).
% 1.97/2.20  thf('206', plain,
% 1.97/2.20      (![X0 : $i, X1 : $i]:
% 1.97/2.20         ((k2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.97/2.20           = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 1.97/2.20      inference('sup-', [status(thm)], ['177', '178'])).
% 1.97/2.20  thf('207', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.97/2.20      inference('sup-', [status(thm)], ['175', '176'])).
% 1.97/2.20  thf('208', plain,
% 1.97/2.20      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.97/2.20         ((m1_subset_1 @ (k2_relset_1 @ X14 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))
% 1.97/2.20          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.97/2.20      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 1.97/2.20  thf('209', plain,
% 1.97/2.20      (![X0 : $i, X1 : $i]:
% 1.97/2.20         (m1_subset_1 @ (k2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0)) @ 
% 1.97/2.20          (k1_zfmisc_1 @ X0))),
% 1.97/2.20      inference('sup-', [status(thm)], ['207', '208'])).
% 1.97/2.20  thf('210', plain,
% 1.97/2.20      (![X0 : $i, X1 : $i]:
% 1.97/2.20         (m1_subset_1 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ 
% 1.97/2.20          (k1_zfmisc_1 @ X0))),
% 1.97/2.20      inference('sup+', [status(thm)], ['206', '209'])).
% 1.97/2.20  thf('211', plain,
% 1.97/2.20      (![X0 : $i]:
% 1.97/2.20         (m1_subset_1 @ (k2_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 1.97/2.20      inference('sup+', [status(thm)], ['205', '210'])).
% 1.97/2.20  thf('212', plain,
% 1.97/2.20      (![X6 : $i, X7 : $i]:
% 1.97/2.20         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 1.97/2.20      inference('cnf', [status(esa)], [t3_subset])).
% 1.97/2.20  thf('213', plain,
% 1.97/2.20      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 1.97/2.20      inference('sup-', [status(thm)], ['211', '212'])).
% 1.97/2.20  thf('214', plain,
% 1.97/2.20      (![X0 : $i, X2 : $i]:
% 1.97/2.20         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.97/2.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.97/2.20  thf('215', plain,
% 1.97/2.20      (![X0 : $i]:
% 1.97/2.20         (~ (r1_tarski @ X0 @ (k2_relat_1 @ k1_xboole_0))
% 1.97/2.20          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 1.97/2.20      inference('sup-', [status(thm)], ['213', '214'])).
% 1.97/2.20  thf('216', plain,
% 1.97/2.20      ((![X0 : $i]:
% 1.97/2.20          (~ (r1_tarski @ X0 @ k1_xboole_0)
% 1.97/2.20           | ((X0) = (k2_relat_1 @ k1_xboole_0))))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('sup-', [status(thm)], ['204', '215'])).
% 1.97/2.20  thf('217', plain,
% 1.97/2.20      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('demod', [status(thm)], ['170', '171', '172', '182', '183'])).
% 1.97/2.20  thf('218', plain,
% 1.97/2.20      ((![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0))))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('demod', [status(thm)], ['216', '217'])).
% 1.97/2.20  thf('219', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 1.97/2.20      inference('sat_resolution*', [status(thm)], ['110', '164', '165'])).
% 1.97/2.20  thf('220', plain,
% 1.97/2.20      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.97/2.20      inference('simpl_trail', [status(thm)], ['218', '219'])).
% 1.97/2.20  thf('221', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.97/2.20      inference('sup-', [status(thm)], ['203', '220'])).
% 1.97/2.20  thf('222', plain, (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A)),
% 1.97/2.20      inference('demod', [status(thm)], ['167', '221'])).
% 1.97/2.20  thf('223', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.97/2.20      inference('sup-', [status(thm)], ['175', '176'])).
% 1.97/2.20  thf('224', plain,
% 1.97/2.20      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 1.97/2.20      inference('simplify', [status(thm)], ['20'])).
% 1.97/2.20  thf('225', plain,
% 1.97/2.20      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.97/2.20         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 1.97/2.20          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.97/2.20      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.97/2.20  thf('226', plain,
% 1.97/2.20      (![X0 : $i, X1 : $i]:
% 1.97/2.20         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.97/2.20          | ((k1_relset_1 @ k1_xboole_0 @ X0 @ X1) = (k1_relat_1 @ X1)))),
% 1.97/2.20      inference('sup-', [status(thm)], ['224', '225'])).
% 1.97/2.20  thf('227', plain,
% 1.97/2.20      (![X0 : $i]:
% 1.97/2.20         ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 1.97/2.20           = (k1_relat_1 @ k1_xboole_0))),
% 1.97/2.20      inference('sup-', [status(thm)], ['223', '226'])).
% 1.97/2.20  thf('228', plain,
% 1.97/2.20      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.97/2.20         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 1.97/2.20          | (v1_funct_2 @ X27 @ X25 @ X26)
% 1.97/2.20          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 1.97/2.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.97/2.20  thf('229', plain,
% 1.97/2.20      (![X0 : $i]:
% 1.97/2.20         (((k1_xboole_0) != (k1_relat_1 @ k1_xboole_0))
% 1.97/2.20          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 1.97/2.20          | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 1.97/2.20      inference('sup-', [status(thm)], ['227', '228'])).
% 1.97/2.20  thf('230', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.97/2.20      inference('sup-', [status(thm)], ['175', '176'])).
% 1.97/2.20  thf('231', plain,
% 1.97/2.20      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 1.97/2.20      inference('simplify', [status(thm)], ['20'])).
% 1.97/2.20  thf('232', plain,
% 1.97/2.20      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.97/2.20         (~ (zip_tseitin_0 @ X28 @ X29)
% 1.97/2.20          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 1.97/2.20          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 1.97/2.20      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.97/2.20  thf('233', plain,
% 1.97/2.20      (![X0 : $i, X1 : $i]:
% 1.97/2.20         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.97/2.20          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 1.97/2.20          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 1.97/2.20      inference('sup-', [status(thm)], ['231', '232'])).
% 1.97/2.20  thf('234', plain,
% 1.97/2.20      (![X23 : $i, X24 : $i]:
% 1.97/2.20         ((zip_tseitin_0 @ X23 @ X24) | ((X24) != (k1_xboole_0)))),
% 1.97/2.20      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.97/2.20  thf('235', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 1.97/2.20      inference('simplify', [status(thm)], ['234'])).
% 1.97/2.20  thf('236', plain,
% 1.97/2.20      (![X0 : $i, X1 : $i]:
% 1.97/2.20         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.97/2.20          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 1.97/2.20      inference('demod', [status(thm)], ['233', '235'])).
% 1.97/2.20  thf('237', plain,
% 1.97/2.20      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.97/2.20      inference('sup-', [status(thm)], ['230', '236'])).
% 1.97/2.20  thf('238', plain,
% 1.97/2.20      (![X0 : $i]:
% 1.97/2.20         (((k1_xboole_0) != (k1_relat_1 @ k1_xboole_0))
% 1.97/2.20          | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 1.97/2.20      inference('demod', [status(thm)], ['229', '237'])).
% 1.97/2.20  thf('239', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.97/2.20      inference('sup-', [status(thm)], ['203', '220'])).
% 1.97/2.20  thf('240', plain,
% 1.97/2.20      (![X10 : $i]:
% 1.97/2.20         (~ (v2_funct_1 @ X10)
% 1.97/2.20          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 1.97/2.20          | ~ (v1_funct_1 @ X10)
% 1.97/2.20          | ~ (v1_relat_1 @ X10))),
% 1.97/2.20      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.97/2.20  thf('241', plain,
% 1.97/2.20      ((((k1_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 1.97/2.20        | ~ (v1_relat_1 @ k1_xboole_0)
% 1.97/2.20        | ~ (v1_funct_1 @ k1_xboole_0)
% 1.97/2.20        | ~ (v2_funct_1 @ k1_xboole_0))),
% 1.97/2.20      inference('sup+', [status(thm)], ['239', '240'])).
% 1.97/2.20  thf('242', plain,
% 1.97/2.20      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('demod', [status(thm)], ['170', '171', '172', '182', '183'])).
% 1.97/2.20  thf('243', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 1.97/2.20      inference('sat_resolution*', [status(thm)], ['110', '164', '165'])).
% 1.97/2.20  thf('244', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.97/2.20      inference('simpl_trail', [status(thm)], ['242', '243'])).
% 1.97/2.20  thf('245', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.97/2.20      inference('sup+', [status(thm)], ['188', '191'])).
% 1.97/2.20  thf('246', plain,
% 1.97/2.20      (((v1_funct_1 @ k1_xboole_0))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('demod', [status(thm)], ['193', '194'])).
% 1.97/2.20  thf('247', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 1.97/2.20      inference('sat_resolution*', [status(thm)], ['110', '164', '165'])).
% 1.97/2.20  thf('248', plain, ((v1_funct_1 @ k1_xboole_0)),
% 1.97/2.20      inference('simpl_trail', [status(thm)], ['246', '247'])).
% 1.97/2.20  thf('249', plain,
% 1.97/2.20      (((v2_funct_1 @ k1_xboole_0))
% 1.97/2.20         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.97/2.20      inference('demod', [status(thm)], ['196', '197'])).
% 1.97/2.20  thf('250', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 1.97/2.20      inference('sat_resolution*', [status(thm)], ['110', '164', '165'])).
% 1.97/2.20  thf('251', plain, ((v2_funct_1 @ k1_xboole_0)),
% 1.97/2.20      inference('simpl_trail', [status(thm)], ['249', '250'])).
% 1.97/2.20  thf('252', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.97/2.20      inference('demod', [status(thm)], ['241', '244', '245', '248', '251'])).
% 1.97/2.20  thf('253', plain,
% 1.97/2.20      (![X0 : $i]:
% 1.97/2.20         (((k1_xboole_0) != (k1_xboole_0))
% 1.97/2.20          | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 1.97/2.20      inference('demod', [status(thm)], ['238', '252'])).
% 1.97/2.20  thf('254', plain,
% 1.97/2.20      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.97/2.20      inference('simplify', [status(thm)], ['253'])).
% 1.97/2.20  thf('255', plain, ($false), inference('demod', [status(thm)], ['222', '254'])).
% 1.97/2.20  
% 1.97/2.20  % SZS output end Refutation
% 1.97/2.20  
% 1.97/2.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

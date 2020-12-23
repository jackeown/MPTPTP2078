%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4LiGxcZ3wv

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:26 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 184 expanded)
%              Number of leaves         :   42 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :  928 (3030 expanded)
%              Number of equality atoms :   65 ( 167 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
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

thf('2',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

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
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('8',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X40 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('9',plain,(
    ! [X39: $i] :
      ( zip_tseitin_0 @ X39 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['10'])).

thf('12',plain,(
    zip_tseitin_1 @ sk_C @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v2_funct_1 @ X21 )
      | ( ( k10_relat_1 @ X21 @ ( k9_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v3_funct_2 @ X36 @ X37 @ X38 )
      | ( v2_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('27',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['18','23','24','30'])).

thf('32',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','31'])).

thf('33',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('36',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k7_relset_1 @ X29 @ X30 @ X28 @ X31 )
        = ( k9_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('39',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k8_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k10_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['34','37','40'])).

thf('42',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v3_funct_2 @ X36 @ X37 @ X38 )
      | ( v2_funct_2 @ X36 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('45',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['45','46','47'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('49',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v2_funct_2 @ X48 @ X47 )
      | ( ( k2_relat_1 @ X48 )
        = X47 )
      | ~ ( v5_relat_1 @ X48 @ X47 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('53',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('54',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['50','51','54'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('56',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k2_relat_1 @ X19 ) )
      | ( ( k9_relat_1 @ X19 @ ( k10_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['42','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('64',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['33'])).

thf('65',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ( sk_B != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
    = sk_B ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['33'])).

thf('70',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['68','69'])).

thf('71',plain,(
    ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['41','70'])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4LiGxcZ3wv
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:13:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.76/0.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.98  % Solved by: fo/fo7.sh
% 0.76/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.98  % done 557 iterations in 0.503s
% 0.76/0.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.98  % SZS output start Refutation
% 0.76/0.98  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.98  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.76/0.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.98  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.76/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.98  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.76/0.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.98  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.76/0.98  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.76/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.98  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.76/0.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.98  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.76/0.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.98  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.76/0.98  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.76/0.98  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.76/0.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.76/0.98  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.76/0.98  thf(t92_funct_2, conjecture,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.76/0.98         ( v3_funct_2 @ C @ A @ A ) & 
% 0.76/0.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.76/0.98       ( ( r1_tarski @ B @ A ) =>
% 0.76/0.98         ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.76/0.98             ( B ) ) & 
% 0.76/0.98           ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.76/0.98             ( B ) ) ) ) ))).
% 0.76/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.98    (~( ![A:$i,B:$i,C:$i]:
% 0.76/0.98        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.76/0.98            ( v3_funct_2 @ C @ A @ A ) & 
% 0.76/0.98            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.76/0.98          ( ( r1_tarski @ B @ A ) =>
% 0.76/0.98            ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.76/0.98                ( B ) ) & 
% 0.76/0.98              ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.76/0.98                ( B ) ) ) ) ) )),
% 0.76/0.98    inference('cnf.neg', [status(esa)], [t92_funct_2])).
% 0.76/0.98  thf('0', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('1', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(d1_funct_2, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.98           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.76/0.98             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.76/0.98         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.98           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.76/0.98             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.76/0.98  thf(zf_stmt_1, axiom,
% 0.76/0.98    (![C:$i,B:$i,A:$i]:
% 0.76/0.98     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.76/0.98       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.76/0.98  thf('2', plain,
% 0.76/0.98      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.76/0.98         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.76/0.98          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 0.76/0.98          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/0.98  thf('3', plain,
% 0.76/0.98      ((~ (zip_tseitin_1 @ sk_C @ sk_A @ sk_A)
% 0.76/0.98        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_C)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/0.98  thf('4', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.76/0.98  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.76/0.98  thf(zf_stmt_4, axiom,
% 0.76/0.98    (![B:$i,A:$i]:
% 0.76/0.98     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.98       ( zip_tseitin_0 @ B @ A ) ))).
% 0.76/0.98  thf(zf_stmt_5, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.76/0.98         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.98           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.76/0.98             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.76/0.98  thf('5', plain,
% 0.76/0.98      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.76/0.98         (~ (zip_tseitin_0 @ X44 @ X45)
% 0.76/0.98          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 0.76/0.98          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/0.98  thf('6', plain,
% 0.76/0.98      (((zip_tseitin_1 @ sk_C @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['4', '5'])).
% 0.76/0.98  thf('7', plain,
% 0.76/0.98      (![X39 : $i, X40 : $i]:
% 0.76/0.98         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.76/0.98  thf('8', plain,
% 0.76/0.98      (![X39 : $i, X40 : $i]:
% 0.76/0.98         ((zip_tseitin_0 @ X39 @ X40) | ((X40) != (k1_xboole_0)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.76/0.98  thf('9', plain, (![X39 : $i]: (zip_tseitin_0 @ X39 @ k1_xboole_0)),
% 0.76/0.98      inference('simplify', [status(thm)], ['8'])).
% 0.76/0.98  thf('10', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.98         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.76/0.98      inference('sup+', [status(thm)], ['7', '9'])).
% 0.76/0.98  thf('11', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.76/0.98      inference('eq_fact', [status(thm)], ['10'])).
% 0.76/0.98  thf('12', plain, ((zip_tseitin_1 @ sk_C @ sk_A @ sk_A)),
% 0.76/0.98      inference('demod', [status(thm)], ['6', '11'])).
% 0.76/0.98  thf('13', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(redefinition_k1_relset_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.76/0.98  thf('14', plain,
% 0.76/0.98      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.76/0.98         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.76/0.98          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.76/0.98  thf('15', plain,
% 0.76/0.98      (((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.76/0.98      inference('sup-', [status(thm)], ['13', '14'])).
% 0.76/0.98  thf('16', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.76/0.98      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.76/0.98  thf(t164_funct_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.76/0.98       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.76/0.98         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.76/0.98  thf('17', plain,
% 0.76/0.98      (![X20 : $i, X21 : $i]:
% 0.76/0.98         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 0.76/0.98          | ~ (v2_funct_1 @ X21)
% 0.76/0.98          | ((k10_relat_1 @ X21 @ (k9_relat_1 @ X21 @ X20)) = (X20))
% 0.76/0.98          | ~ (v1_funct_1 @ X21)
% 0.76/0.98          | ~ (v1_relat_1 @ X21))),
% 0.76/0.98      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.76/0.98  thf('18', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (r1_tarski @ X0 @ sk_A)
% 0.76/0.98          | ~ (v1_relat_1 @ sk_C)
% 0.76/0.98          | ~ (v1_funct_1 @ sk_C)
% 0.76/0.98          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0))
% 0.76/0.98          | ~ (v2_funct_1 @ sk_C))),
% 0.76/0.98      inference('sup-', [status(thm)], ['16', '17'])).
% 0.76/0.98  thf('19', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(cc2_relat_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ A ) =>
% 0.76/0.98       ( ![B:$i]:
% 0.76/0.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.76/0.98  thf('20', plain,
% 0.76/0.98      (![X10 : $i, X11 : $i]:
% 0.76/0.98         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.76/0.98          | (v1_relat_1 @ X10)
% 0.76/0.98          | ~ (v1_relat_1 @ X11))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.76/0.98  thf('21', plain,
% 0.76/0.98      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.76/0.98      inference('sup-', [status(thm)], ['19', '20'])).
% 0.76/0.98  thf(fc6_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.76/0.98  thf('22', plain,
% 0.76/0.98      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 0.76/0.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.76/0.98  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.98      inference('demod', [status(thm)], ['21', '22'])).
% 0.76/0.98  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('25', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(cc2_funct_2, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.76/0.98         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.76/0.98  thf('26', plain,
% 0.76/0.98      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.76/0.98         (~ (v1_funct_1 @ X36)
% 0.76/0.98          | ~ (v3_funct_2 @ X36 @ X37 @ X38)
% 0.76/0.98          | (v2_funct_1 @ X36)
% 0.76/0.98          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.76/0.98  thf('27', plain,
% 0.76/0.98      (((v2_funct_1 @ sk_C)
% 0.76/0.98        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.76/0.98        | ~ (v1_funct_1 @ sk_C))),
% 0.76/0.98      inference('sup-', [status(thm)], ['25', '26'])).
% 0.76/0.98  thf('28', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('30', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.98      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.76/0.98  thf('31', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (r1_tarski @ X0 @ sk_A)
% 0.76/0.98          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.76/0.98      inference('demod', [status(thm)], ['18', '23', '24', '30'])).
% 0.76/0.98  thf('32', plain,
% 0.76/0.98      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.76/0.98      inference('sup-', [status(thm)], ['0', '31'])).
% 0.76/0.98  thf('33', plain,
% 0.76/0.98      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.76/0.98          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B))
% 0.76/0.98        | ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.76/0.98            (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('34', plain,
% 0.76/0.98      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.76/0.98          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.76/0.98         <= (~
% 0.76/0.98             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.76/0.98                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.76/0.98      inference('split', [status(esa)], ['33'])).
% 0.76/0.98  thf('35', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(redefinition_k7_relset_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.76/0.98  thf('36', plain,
% 0.76/0.98      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.76/0.98         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.76/0.98          | ((k7_relset_1 @ X29 @ X30 @ X28 @ X31) = (k9_relat_1 @ X28 @ X31)))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.76/0.98  thf('37', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['35', '36'])).
% 0.76/0.98  thf('38', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(redefinition_k8_relset_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.76/0.98  thf('39', plain,
% 0.76/0.98      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.76/0.98         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.76/0.98          | ((k8_relset_1 @ X33 @ X34 @ X32 @ X35) = (k10_relat_1 @ X32 @ X35)))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.76/0.98  thf('40', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['38', '39'])).
% 0.76/0.98  thf('41', plain,
% 0.76/0.98      ((((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B)))
% 0.76/0.98         <= (~
% 0.76/0.98             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.76/0.98                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.76/0.98      inference('demod', [status(thm)], ['34', '37', '40'])).
% 0.76/0.98  thf('42', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('43', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('44', plain,
% 0.76/0.98      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.76/0.98         (~ (v1_funct_1 @ X36)
% 0.76/0.98          | ~ (v3_funct_2 @ X36 @ X37 @ X38)
% 0.76/0.98          | (v2_funct_2 @ X36 @ X38)
% 0.76/0.98          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.76/0.98  thf('45', plain,
% 0.76/0.98      (((v2_funct_2 @ sk_C @ sk_A)
% 0.76/0.98        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.76/0.98        | ~ (v1_funct_1 @ sk_C))),
% 0.76/0.98      inference('sup-', [status(thm)], ['43', '44'])).
% 0.76/0.98  thf('46', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('48', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.76/0.98      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.76/0.98  thf(d3_funct_2, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.76/0.98       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.76/0.98  thf('49', plain,
% 0.76/0.98      (![X47 : $i, X48 : $i]:
% 0.76/0.98         (~ (v2_funct_2 @ X48 @ X47)
% 0.76/0.98          | ((k2_relat_1 @ X48) = (X47))
% 0.76/0.98          | ~ (v5_relat_1 @ X48 @ X47)
% 0.76/0.98          | ~ (v1_relat_1 @ X48))),
% 0.76/0.98      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.76/0.98  thf('50', plain,
% 0.76/0.98      ((~ (v1_relat_1 @ sk_C)
% 0.76/0.98        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.76/0.98        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['48', '49'])).
% 0.76/0.98  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.98      inference('demod', [status(thm)], ['21', '22'])).
% 0.76/0.98  thf('52', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(cc2_relset_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.76/0.98  thf('53', plain,
% 0.76/0.98      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.76/0.98         ((v5_relat_1 @ X22 @ X24)
% 0.76/0.98          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/0.98  thf('54', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.76/0.98      inference('sup-', [status(thm)], ['52', '53'])).
% 0.76/0.98  thf('55', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['50', '51', '54'])).
% 0.76/0.98  thf(t147_funct_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.76/0.98       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.76/0.98         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.76/0.98  thf('56', plain,
% 0.76/0.98      (![X18 : $i, X19 : $i]:
% 0.76/0.98         (~ (r1_tarski @ X18 @ (k2_relat_1 @ X19))
% 0.76/0.98          | ((k9_relat_1 @ X19 @ (k10_relat_1 @ X19 @ X18)) = (X18))
% 0.76/0.98          | ~ (v1_funct_1 @ X19)
% 0.76/0.98          | ~ (v1_relat_1 @ X19))),
% 0.76/0.98      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.76/0.98  thf('57', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (r1_tarski @ X0 @ sk_A)
% 0.76/0.98          | ~ (v1_relat_1 @ sk_C)
% 0.76/0.98          | ~ (v1_funct_1 @ sk_C)
% 0.76/0.98          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['55', '56'])).
% 0.76/0.98  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.98      inference('demod', [status(thm)], ['21', '22'])).
% 0.76/0.98  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('60', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (r1_tarski @ X0 @ sk_A)
% 0.76/0.98          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.76/0.98      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.76/0.98  thf('61', plain,
% 0.76/0.98      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.76/0.98      inference('sup-', [status(thm)], ['42', '60'])).
% 0.76/0.98  thf('62', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['38', '39'])).
% 0.76/0.98  thf('63', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['35', '36'])).
% 0.76/0.98  thf('64', plain,
% 0.76/0.98      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.76/0.98          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.76/0.98         <= (~
% 0.76/0.98             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.76/0.98                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.76/0.98      inference('split', [status(esa)], ['33'])).
% 0.76/0.98  thf('65', plain,
% 0.76/0.98      ((((k9_relat_1 @ sk_C @ (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B))
% 0.76/0.98          != (sk_B)))
% 0.76/0.98         <= (~
% 0.76/0.98             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.76/0.98                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['63', '64'])).
% 0.76/0.98  thf('66', plain,
% 0.76/0.98      ((((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) != (sk_B)))
% 0.76/0.98         <= (~
% 0.76/0.98             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.76/0.98                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['62', '65'])).
% 0.76/0.98  thf('67', plain,
% 0.76/0.98      ((((sk_B) != (sk_B)))
% 0.76/0.98         <= (~
% 0.76/0.98             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.76/0.98                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['61', '66'])).
% 0.76/0.98  thf('68', plain,
% 0.76/0.98      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.76/0.98          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.76/0.98      inference('simplify', [status(thm)], ['67'])).
% 0.76/0.98  thf('69', plain,
% 0.76/0.98      (~
% 0.76/0.98       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.76/0.98          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))) | 
% 0.76/0.98       ~
% 0.76/0.98       (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.76/0.98          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.76/0.98      inference('split', [status(esa)], ['33'])).
% 0.76/0.98  thf('70', plain,
% 0.76/0.98      (~
% 0.76/0.98       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.76/0.98          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.76/0.98      inference('sat_resolution*', [status(thm)], ['68', '69'])).
% 0.76/0.98  thf('71', plain,
% 0.76/0.98      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B))),
% 0.76/0.98      inference('simpl_trail', [status(thm)], ['41', '70'])).
% 0.76/0.98  thf('72', plain, ($false),
% 0.76/0.98      inference('simplify_reflect-', [status(thm)], ['32', '71'])).
% 0.76/0.98  
% 0.76/0.98  % SZS output end Refutation
% 0.76/0.98  
% 0.76/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

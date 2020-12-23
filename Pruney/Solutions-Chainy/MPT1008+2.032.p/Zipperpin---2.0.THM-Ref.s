%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oWk1d4RhY4

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:35 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 390 expanded)
%              Number of leaves         :   49 ( 139 expanded)
%              Depth                    :   14
%              Number of atoms          :  871 (4597 expanded)
%              Number of equality atoms :   83 ( 329 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2 != X1 )
      | ( r2_hidden @ X2 @ X3 )
      | ( X3
       != ( k2_tarski @ X4 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X1: $i,X4: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X4 @ X1 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

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

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf('5',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( ( k1_relset_1 @ X39 @ X40 @ X41 )
       != X39 )
      | ~ ( r2_hidden @ X42 @ X39 )
      | ( r2_hidden @ ( k4_tarski @ X42 @ ( sk_E @ X42 @ X41 ) ) @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
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

thf('8',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_2 @ X48 @ X46 @ X47 )
      | ( X46
        = ( k1_relset_1 @ X46 @ X47 @ X48 ) )
      | ~ ( zip_tseitin_1 @ X48 @ X47 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X44: $i,X45: $i] :
      ( ( zip_tseitin_0 @ X44 @ X45 )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('12',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( zip_tseitin_0 @ X49 @ X50 )
      | ( zip_tseitin_1 @ X51 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_E @ sk_A @ sk_C ) ) @ sk_C ),
    inference('sup-',[status(thm)],['3','19'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('21',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('22',plain,(
    ~ ( r1_tarski @ sk_C @ ( k4_tarski @ sk_A @ ( sk_E @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v4_relat_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('25',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23
        = ( k7_relat_1 @ X23 @ X24 ) )
      | ~ ( v4_relat_1 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('29',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) )
        = ( k9_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('33',plain,(
    ! [X25: $i] :
      ( ( ( k2_relat_1 @ X25 )
       != k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['28','29'])).

thf('37',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['28','29'])).

thf('39',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('40',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) )
        = ( k9_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('41',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['28','29'])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36','37','38','43'])).

thf('45',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('46',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k11_relat_1 @ X21 @ X22 )
        = k1_xboole_0 )
      | ( r2_hidden @ X22 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf(t168_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('47',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X27 ) )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X27 @ ( k1_tarski @ X26 ) ) )
        = ( k1_tarski @ ( k1_funct_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t168_funct_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_tarski @ X1 ) ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_tarski @ X1 ) ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k11_relat_1 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['45','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('52',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k11_relat_1 @ X17 @ X18 )
        = ( k9_relat_1 @ X17 @ ( k1_tarski @ X18 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('54',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k11_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['28','29'])).

thf('56',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k11_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51','56','57'])).

thf('59',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('61',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X38 @ X36 )
        = ( k2_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('62',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['58','63'])).

thf('65',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','64'])).

thf('66',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['65'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['22','66','67','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oWk1d4RhY4
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:42:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.65/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.65/0.82  % Solved by: fo/fo7.sh
% 0.65/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.82  % done 627 iterations in 0.393s
% 0.65/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.65/0.82  % SZS output start Refutation
% 0.65/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.82  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.65/0.82  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.65/0.82  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.65/0.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.65/0.82  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.65/0.82  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.65/0.82  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.65/0.82  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 0.65/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.65/0.82  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.65/0.82  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.65/0.82  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.65/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.65/0.82  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.65/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.65/0.82  thf(sk_C_type, type, sk_C: $i).
% 0.65/0.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.65/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.65/0.82  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.65/0.82  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.65/0.82  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.65/0.82  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.65/0.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.65/0.82  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.65/0.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.65/0.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.65/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.65/0.82  thf(t69_enumset1, axiom,
% 0.65/0.82    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.65/0.82  thf('0', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.65/0.82      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.65/0.82  thf(d2_tarski, axiom,
% 0.65/0.82    (![A:$i,B:$i,C:$i]:
% 0.65/0.82     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.65/0.82       ( ![D:$i]:
% 0.65/0.82         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.65/0.82  thf('1', plain,
% 0.65/0.82      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.65/0.82         (((X2) != (X1))
% 0.65/0.82          | (r2_hidden @ X2 @ X3)
% 0.65/0.82          | ((X3) != (k2_tarski @ X4 @ X1)))),
% 0.65/0.82      inference('cnf', [status(esa)], [d2_tarski])).
% 0.65/0.82  thf('2', plain,
% 0.65/0.82      (![X1 : $i, X4 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X4 @ X1))),
% 0.65/0.82      inference('simplify', [status(thm)], ['1'])).
% 0.65/0.82  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.65/0.82      inference('sup+', [status(thm)], ['0', '2'])).
% 0.65/0.82  thf(t62_funct_2, conjecture,
% 0.65/0.82    (![A:$i,B:$i,C:$i]:
% 0.65/0.82     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.65/0.82         ( m1_subset_1 @
% 0.65/0.82           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.65/0.82       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.65/0.82         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.65/0.82           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.65/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.82    (~( ![A:$i,B:$i,C:$i]:
% 0.65/0.82        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.65/0.82            ( m1_subset_1 @
% 0.65/0.82              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.65/0.82          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.65/0.82            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.65/0.82              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.65/0.82    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.65/0.82  thf('4', plain,
% 0.65/0.82      ((m1_subset_1 @ sk_C @ 
% 0.65/0.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf(t22_relset_1, axiom,
% 0.65/0.82    (![A:$i,B:$i,C:$i]:
% 0.65/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.65/0.82       ( ( ![D:$i]:
% 0.65/0.82           ( ~( ( r2_hidden @ D @ B ) & 
% 0.65/0.82                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.65/0.82         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.65/0.82  thf('5', plain,
% 0.65/0.82      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.65/0.82         (((k1_relset_1 @ X39 @ X40 @ X41) != (X39))
% 0.65/0.82          | ~ (r2_hidden @ X42 @ X39)
% 0.65/0.82          | (r2_hidden @ (k4_tarski @ X42 @ (sk_E @ X42 @ X41)) @ X41)
% 0.65/0.82          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.65/0.82      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.65/0.82  thf('6', plain,
% 0.65/0.82      (![X0 : $i]:
% 0.65/0.82         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C)
% 0.65/0.82          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.65/0.82          | ((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 0.65/0.82              != (k1_tarski @ sk_A)))),
% 0.65/0.82      inference('sup-', [status(thm)], ['4', '5'])).
% 0.65/0.82  thf('7', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf(d1_funct_2, axiom,
% 0.65/0.82    (![A:$i,B:$i,C:$i]:
% 0.65/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.65/0.82       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.65/0.82           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.65/0.82             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.65/0.82         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.65/0.82           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.65/0.82             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.65/0.82  thf(zf_stmt_1, axiom,
% 0.65/0.82    (![C:$i,B:$i,A:$i]:
% 0.65/0.82     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.65/0.82       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.65/0.82  thf('8', plain,
% 0.65/0.82      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.65/0.82         (~ (v1_funct_2 @ X48 @ X46 @ X47)
% 0.65/0.82          | ((X46) = (k1_relset_1 @ X46 @ X47 @ X48))
% 0.65/0.82          | ~ (zip_tseitin_1 @ X48 @ X47 @ X46))),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.65/0.82  thf('9', plain,
% 0.65/0.82      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.65/0.82        | ((k1_tarski @ sk_A)
% 0.65/0.82            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 0.65/0.82      inference('sup-', [status(thm)], ['7', '8'])).
% 0.65/0.82  thf(zf_stmt_2, axiom,
% 0.65/0.82    (![B:$i,A:$i]:
% 0.65/0.82     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.65/0.82       ( zip_tseitin_0 @ B @ A ) ))).
% 0.65/0.82  thf('10', plain,
% 0.65/0.82      (![X44 : $i, X45 : $i]:
% 0.65/0.82         ((zip_tseitin_0 @ X44 @ X45) | ((X44) = (k1_xboole_0)))),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.65/0.82  thf('11', plain,
% 0.65/0.82      ((m1_subset_1 @ sk_C @ 
% 0.65/0.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.65/0.82  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.65/0.82  thf(zf_stmt_5, axiom,
% 0.65/0.82    (![A:$i,B:$i,C:$i]:
% 0.65/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.65/0.82       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.65/0.82         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.65/0.82           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.65/0.82             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.65/0.82  thf('12', plain,
% 0.65/0.82      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.65/0.82         (~ (zip_tseitin_0 @ X49 @ X50)
% 0.65/0.82          | (zip_tseitin_1 @ X51 @ X49 @ X50)
% 0.65/0.82          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49))))),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.65/0.82  thf('13', plain,
% 0.65/0.82      (((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.65/0.82        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.65/0.82      inference('sup-', [status(thm)], ['11', '12'])).
% 0.65/0.82  thf('14', plain,
% 0.65/0.82      ((((sk_B) = (k1_xboole_0))
% 0.65/0.82        | (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 0.65/0.82      inference('sup-', [status(thm)], ['10', '13'])).
% 0.65/0.82  thf('15', plain, (((sk_B) != (k1_xboole_0))),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf('16', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 0.65/0.82      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.65/0.82  thf('17', plain,
% 0.65/0.82      (((k1_tarski @ sk_A) = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C))),
% 0.65/0.82      inference('demod', [status(thm)], ['9', '16'])).
% 0.65/0.82  thf('18', plain,
% 0.65/0.82      (![X0 : $i]:
% 0.65/0.82         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C)
% 0.65/0.82          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.65/0.82          | ((k1_tarski @ sk_A) != (k1_tarski @ sk_A)))),
% 0.65/0.82      inference('demod', [status(thm)], ['6', '17'])).
% 0.65/0.82  thf('19', plain,
% 0.65/0.82      (![X0 : $i]:
% 0.65/0.82         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.65/0.82          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C))),
% 0.65/0.82      inference('simplify', [status(thm)], ['18'])).
% 0.65/0.82  thf('20', plain,
% 0.65/0.82      ((r2_hidden @ (k4_tarski @ sk_A @ (sk_E @ sk_A @ sk_C)) @ sk_C)),
% 0.65/0.82      inference('sup-', [status(thm)], ['3', '19'])).
% 0.65/0.82  thf(t7_ordinal1, axiom,
% 0.65/0.82    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.65/0.82  thf('21', plain,
% 0.65/0.82      (![X28 : $i, X29 : $i]:
% 0.65/0.82         (~ (r2_hidden @ X28 @ X29) | ~ (r1_tarski @ X29 @ X28))),
% 0.65/0.82      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.65/0.82  thf('22', plain,
% 0.65/0.82      (~ (r1_tarski @ sk_C @ (k4_tarski @ sk_A @ (sk_E @ sk_A @ sk_C)))),
% 0.65/0.82      inference('sup-', [status(thm)], ['20', '21'])).
% 0.65/0.82  thf('23', plain,
% 0.65/0.82      ((m1_subset_1 @ sk_C @ 
% 0.65/0.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf(cc2_relset_1, axiom,
% 0.65/0.82    (![A:$i,B:$i,C:$i]:
% 0.65/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.65/0.82       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.65/0.82  thf('24', plain,
% 0.65/0.82      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.65/0.82         ((v4_relat_1 @ X33 @ X34)
% 0.65/0.82          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.65/0.82      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.65/0.82  thf('25', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.65/0.82      inference('sup-', [status(thm)], ['23', '24'])).
% 0.65/0.82  thf(t209_relat_1, axiom,
% 0.65/0.82    (![A:$i,B:$i]:
% 0.65/0.82     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.65/0.82       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.65/0.82  thf('26', plain,
% 0.65/0.82      (![X23 : $i, X24 : $i]:
% 0.65/0.82         (((X23) = (k7_relat_1 @ X23 @ X24))
% 0.65/0.82          | ~ (v4_relat_1 @ X23 @ X24)
% 0.65/0.82          | ~ (v1_relat_1 @ X23))),
% 0.65/0.82      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.65/0.82  thf('27', plain,
% 0.65/0.82      ((~ (v1_relat_1 @ sk_C)
% 0.65/0.82        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A))))),
% 0.65/0.82      inference('sup-', [status(thm)], ['25', '26'])).
% 0.65/0.82  thf('28', plain,
% 0.65/0.82      ((m1_subset_1 @ sk_C @ 
% 0.65/0.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf(cc1_relset_1, axiom,
% 0.65/0.82    (![A:$i,B:$i,C:$i]:
% 0.65/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.65/0.82       ( v1_relat_1 @ C ) ))).
% 0.65/0.82  thf('29', plain,
% 0.65/0.82      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.65/0.82         ((v1_relat_1 @ X30)
% 0.65/0.82          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.65/0.82      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.65/0.82  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.65/0.82      inference('sup-', [status(thm)], ['28', '29'])).
% 0.65/0.82  thf('31', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.65/0.82      inference('demod', [status(thm)], ['27', '30'])).
% 0.65/0.82  thf(t148_relat_1, axiom,
% 0.65/0.82    (![A:$i,B:$i]:
% 0.65/0.82     ( ( v1_relat_1 @ B ) =>
% 0.65/0.82       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.65/0.82  thf('32', plain,
% 0.65/0.82      (![X19 : $i, X20 : $i]:
% 0.65/0.82         (((k2_relat_1 @ (k7_relat_1 @ X19 @ X20)) = (k9_relat_1 @ X19 @ X20))
% 0.65/0.82          | ~ (v1_relat_1 @ X19))),
% 0.65/0.82      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.65/0.82  thf(t64_relat_1, axiom,
% 0.65/0.82    (![A:$i]:
% 0.65/0.82     ( ( v1_relat_1 @ A ) =>
% 0.65/0.82       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.65/0.82           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.65/0.82         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.65/0.82  thf('33', plain,
% 0.65/0.82      (![X25 : $i]:
% 0.65/0.82         (((k2_relat_1 @ X25) != (k1_xboole_0))
% 0.65/0.82          | ((X25) = (k1_xboole_0))
% 0.65/0.82          | ~ (v1_relat_1 @ X25))),
% 0.65/0.82      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.65/0.82  thf('34', plain,
% 0.65/0.82      (![X0 : $i, X1 : $i]:
% 0.65/0.82         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.65/0.82          | ~ (v1_relat_1 @ X1)
% 0.65/0.82          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.65/0.82          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.65/0.82      inference('sup-', [status(thm)], ['32', '33'])).
% 0.65/0.82  thf('35', plain,
% 0.65/0.82      ((~ (v1_relat_1 @ sk_C)
% 0.65/0.82        | ((k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.65/0.82        | ~ (v1_relat_1 @ sk_C)
% 0.65/0.82        | ((k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)) != (k1_xboole_0)))),
% 0.65/0.82      inference('sup-', [status(thm)], ['31', '34'])).
% 0.65/0.82  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.65/0.82      inference('sup-', [status(thm)], ['28', '29'])).
% 0.65/0.82  thf('37', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.65/0.82      inference('demod', [status(thm)], ['27', '30'])).
% 0.65/0.82  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.65/0.82      inference('sup-', [status(thm)], ['28', '29'])).
% 0.65/0.82  thf('39', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.65/0.82      inference('demod', [status(thm)], ['27', '30'])).
% 0.65/0.82  thf('40', plain,
% 0.65/0.82      (![X19 : $i, X20 : $i]:
% 0.65/0.82         (((k2_relat_1 @ (k7_relat_1 @ X19 @ X20)) = (k9_relat_1 @ X19 @ X20))
% 0.65/0.82          | ~ (v1_relat_1 @ X19))),
% 0.65/0.82      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.65/0.82  thf('41', plain,
% 0.65/0.82      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))
% 0.65/0.82        | ~ (v1_relat_1 @ sk_C))),
% 0.65/0.82      inference('sup+', [status(thm)], ['39', '40'])).
% 0.65/0.82  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.65/0.82      inference('sup-', [status(thm)], ['28', '29'])).
% 0.65/0.82  thf('43', plain,
% 0.65/0.82      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.65/0.82      inference('demod', [status(thm)], ['41', '42'])).
% 0.65/0.82  thf('44', plain,
% 0.65/0.82      ((((sk_C) = (k1_xboole_0)) | ((k2_relat_1 @ sk_C) != (k1_xboole_0)))),
% 0.65/0.82      inference('demod', [status(thm)], ['35', '36', '37', '38', '43'])).
% 0.65/0.82  thf('45', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.65/0.82      inference('demod', [status(thm)], ['27', '30'])).
% 0.65/0.82  thf(t205_relat_1, axiom,
% 0.65/0.82    (![A:$i,B:$i]:
% 0.65/0.82     ( ( v1_relat_1 @ B ) =>
% 0.65/0.82       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.65/0.82         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.65/0.82  thf('46', plain,
% 0.65/0.82      (![X21 : $i, X22 : $i]:
% 0.65/0.82         (((k11_relat_1 @ X21 @ X22) = (k1_xboole_0))
% 0.65/0.82          | (r2_hidden @ X22 @ (k1_relat_1 @ X21))
% 0.65/0.82          | ~ (v1_relat_1 @ X21))),
% 0.65/0.82      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.65/0.82  thf(t168_funct_1, axiom,
% 0.65/0.82    (![A:$i,B:$i]:
% 0.65/0.82     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.65/0.82       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.65/0.82         ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) =
% 0.65/0.82           ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.65/0.82  thf('47', plain,
% 0.65/0.82      (![X26 : $i, X27 : $i]:
% 0.65/0.82         (~ (r2_hidden @ X26 @ (k1_relat_1 @ X27))
% 0.65/0.82          | ((k2_relat_1 @ (k7_relat_1 @ X27 @ (k1_tarski @ X26)))
% 0.65/0.82              = (k1_tarski @ (k1_funct_1 @ X27 @ X26)))
% 0.65/0.82          | ~ (v1_funct_1 @ X27)
% 0.65/0.82          | ~ (v1_relat_1 @ X27))),
% 0.65/0.82      inference('cnf', [status(esa)], [t168_funct_1])).
% 0.65/0.82  thf('48', plain,
% 0.65/0.82      (![X0 : $i, X1 : $i]:
% 0.65/0.82         (~ (v1_relat_1 @ X0)
% 0.65/0.82          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.65/0.82          | ~ (v1_relat_1 @ X0)
% 0.65/0.82          | ~ (v1_funct_1 @ X0)
% 0.65/0.82          | ((k2_relat_1 @ (k7_relat_1 @ X0 @ (k1_tarski @ X1)))
% 0.65/0.82              = (k1_tarski @ (k1_funct_1 @ X0 @ X1))))),
% 0.65/0.82      inference('sup-', [status(thm)], ['46', '47'])).
% 0.65/0.82  thf('49', plain,
% 0.65/0.82      (![X0 : $i, X1 : $i]:
% 0.65/0.82         (((k2_relat_1 @ (k7_relat_1 @ X0 @ (k1_tarski @ X1)))
% 0.65/0.82            = (k1_tarski @ (k1_funct_1 @ X0 @ X1)))
% 0.65/0.82          | ~ (v1_funct_1 @ X0)
% 0.65/0.82          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.65/0.82          | ~ (v1_relat_1 @ X0))),
% 0.65/0.82      inference('simplify', [status(thm)], ['48'])).
% 0.65/0.82  thf('50', plain,
% 0.65/0.82      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.65/0.82        | ~ (v1_relat_1 @ sk_C)
% 0.65/0.82        | ((k11_relat_1 @ sk_C @ sk_A) = (k1_xboole_0))
% 0.65/0.82        | ~ (v1_funct_1 @ sk_C))),
% 0.65/0.82      inference('sup+', [status(thm)], ['45', '49'])).
% 0.65/0.82  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.65/0.82      inference('sup-', [status(thm)], ['28', '29'])).
% 0.65/0.82  thf(d16_relat_1, axiom,
% 0.65/0.82    (![A:$i]:
% 0.65/0.82     ( ( v1_relat_1 @ A ) =>
% 0.65/0.82       ( ![B:$i]:
% 0.65/0.82         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.65/0.82  thf('52', plain,
% 0.65/0.82      (![X17 : $i, X18 : $i]:
% 0.65/0.82         (((k11_relat_1 @ X17 @ X18) = (k9_relat_1 @ X17 @ (k1_tarski @ X18)))
% 0.65/0.82          | ~ (v1_relat_1 @ X17))),
% 0.65/0.82      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.65/0.82  thf('53', plain,
% 0.65/0.82      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.65/0.82      inference('demod', [status(thm)], ['41', '42'])).
% 0.65/0.82  thf('54', plain,
% 0.65/0.82      ((((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))
% 0.65/0.82        | ~ (v1_relat_1 @ sk_C))),
% 0.65/0.82      inference('sup+', [status(thm)], ['52', '53'])).
% 0.65/0.82  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 0.65/0.82      inference('sup-', [status(thm)], ['28', '29'])).
% 0.65/0.82  thf('56', plain, (((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))),
% 0.65/0.82      inference('demod', [status(thm)], ['54', '55'])).
% 0.65/0.82  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf('58', plain,
% 0.65/0.82      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.65/0.82        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.65/0.82      inference('demod', [status(thm)], ['50', '51', '56', '57'])).
% 0.65/0.82  thf('59', plain,
% 0.65/0.82      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 0.65/0.82         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf('60', plain,
% 0.65/0.82      ((m1_subset_1 @ sk_C @ 
% 0.65/0.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.65/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.82  thf(redefinition_k2_relset_1, axiom,
% 0.65/0.82    (![A:$i,B:$i,C:$i]:
% 0.65/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.65/0.82       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.65/0.82  thf('61', plain,
% 0.65/0.82      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.65/0.82         (((k2_relset_1 @ X37 @ X38 @ X36) = (k2_relat_1 @ X36))
% 0.65/0.82          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.65/0.82      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.65/0.82  thf('62', plain,
% 0.65/0.82      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.65/0.82      inference('sup-', [status(thm)], ['60', '61'])).
% 0.65/0.82  thf('63', plain,
% 0.65/0.82      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.65/0.82      inference('demod', [status(thm)], ['59', '62'])).
% 0.65/0.82  thf('64', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.65/0.82      inference('simplify_reflect-', [status(thm)], ['58', '63'])).
% 0.65/0.82  thf('65', plain,
% 0.65/0.82      ((((sk_C) = (k1_xboole_0)) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.65/0.82      inference('demod', [status(thm)], ['44', '64'])).
% 0.65/0.82  thf('66', plain, (((sk_C) = (k1_xboole_0))),
% 0.65/0.82      inference('simplify', [status(thm)], ['65'])).
% 0.65/0.82  thf('67', plain, (((sk_C) = (k1_xboole_0))),
% 0.65/0.82      inference('simplify', [status(thm)], ['65'])).
% 0.65/0.82  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.65/0.82  thf('68', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.65/0.82      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.65/0.82  thf('69', plain, ($false),
% 0.65/0.82      inference('demod', [status(thm)], ['22', '66', '67', '68'])).
% 0.65/0.82  
% 0.65/0.82  % SZS output end Refutation
% 0.65/0.82  
% 0.65/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

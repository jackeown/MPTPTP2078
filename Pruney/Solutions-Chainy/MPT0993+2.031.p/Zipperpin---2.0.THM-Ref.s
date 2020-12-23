%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fK5Rpoi6Tg

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:49 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  151 (1048 expanded)
%              Number of leaves         :   42 ( 316 expanded)
%              Depth                    :   20
%              Number of atoms          : 1050 (13990 expanded)
%              Number of equality atoms :   83 ( 459 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t40_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ A @ C )
       => ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ A @ C )
         => ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ( ( k2_partfun1 @ X34 @ X35 @ X33 @ X36 )
        = ( k7_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    r1_tarski @ sk_A @ sk_C ),
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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('10',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( r1_tarski @ sk_D @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('18',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( r1_tarski @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('21',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('22',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_D = sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','40'])).

thf('42',plain,
    ( ( sk_D = sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( sk_D = sk_B )
      | ~ ( v1_relat_1 @ sk_D )
      | ( v4_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('46',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( sk_D = sk_B )
      | ( v4_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,
    ( ( v4_relat_1 @ sk_D @ sk_C )
    | ( sk_D = sk_B ) ),
    inference('sup-',[status(thm)],['7','48'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('50',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('51',plain,
    ( ( sk_D = sk_B )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['45','46'])).

thf('53',plain,
    ( ( sk_D = sk_B )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('55',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D )
    | ( sk_D = sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( r2_hidden @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf('57',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( r2_relset_1 @ X38 @ X39 @ X40 @ X37 )
      | ( ( k1_funct_1 @ X40 @ ( sk_E @ X37 @ X40 @ X38 ) )
       != ( k1_funct_1 @ X37 @ ( sk_E @ X37 @ X40 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t18_funct_2])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(eq_res,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
    | ( r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    sk_D = sk_B ),
    inference(demod,[status(thm)],['55','63'])).

thf('65',plain,(
    sk_D = sk_B ),
    inference(demod,[status(thm)],['55','63'])).

thf('66',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k7_relat_1 @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','64','65'])).

thf('67',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('69',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('70',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('72',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( v4_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['45','46'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( v4_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v4_relat_1 @ sk_D @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','76'])).

thf('78',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('79',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['45','46'])).

thf('81',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('83',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('85',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['83','84'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('87',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X17 @ X18 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('88',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('93',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('94',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('96',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','96'])).

thf('98',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['83','84'])).

thf('99',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('100',plain,(
    sk_D = sk_B ),
    inference(demod,[status(thm)],['55','63'])).

thf('101',plain,(
    sk_D = sk_B ),
    inference(demod,[status(thm)],['55','63'])).

thf('102',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['83','84'])).

thf('104',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['83','84'])).

thf('105',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['83','84'])).

thf('106',plain,(
    r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['102','103','104','105'])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['66','85','86','97','98','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fK5Rpoi6Tg
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:37:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.71/0.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.71/0.90  % Solved by: fo/fo7.sh
% 0.71/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.90  % done 652 iterations in 0.430s
% 0.71/0.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.71/0.90  % SZS output start Refutation
% 0.71/0.90  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.71/0.90  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.71/0.90  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.71/0.90  thf(sk_D_type, type, sk_D: $i).
% 0.71/0.90  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.71/0.90  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.71/0.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.71/0.90  thf(sk_C_type, type, sk_C: $i).
% 0.71/0.90  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.71/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.71/0.90  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.71/0.90  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.71/0.90  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.71/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.71/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.90  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.71/0.90  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.71/0.90  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.71/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.71/0.90  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.71/0.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.71/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.71/0.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.71/0.90  thf(t40_funct_2, conjecture,
% 0.71/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.90     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.71/0.90         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.71/0.90       ( ( r1_tarski @ A @ C ) =>
% 0.71/0.90         ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ))).
% 0.71/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.90    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.90        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.71/0.90            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.71/0.90          ( ( r1_tarski @ A @ C ) =>
% 0.71/0.90            ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) )),
% 0.71/0.90    inference('cnf.neg', [status(esa)], [t40_funct_2])).
% 0.71/0.90  thf('0', plain,
% 0.71/0.90      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.71/0.90          (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_D)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('1', plain,
% 0.71/0.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(redefinition_k2_partfun1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.90     ( ( ( v1_funct_1 @ C ) & 
% 0.71/0.90         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.71/0.90       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.71/0.90  thf('2', plain,
% 0.71/0.90      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.71/0.90         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.71/0.90          | ~ (v1_funct_1 @ X33)
% 0.71/0.90          | ((k2_partfun1 @ X34 @ X35 @ X33 @ X36) = (k7_relat_1 @ X33 @ X36)))),
% 0.71/0.90      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.71/0.90  thf('3', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 0.71/0.90          | ~ (v1_funct_1 @ sk_D))),
% 0.71/0.90      inference('sup-', [status(thm)], ['1', '2'])).
% 0.71/0.90  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('5', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['3', '4'])).
% 0.71/0.90  thf('6', plain,
% 0.71/0.90      (~ (r2_relset_1 @ sk_A @ sk_B @ (k7_relat_1 @ sk_D @ sk_C) @ sk_D)),
% 0.71/0.90      inference('demod', [status(thm)], ['0', '5'])).
% 0.71/0.90  thf('7', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(d1_funct_2, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.90       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.71/0.90           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.71/0.90             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.71/0.90         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.71/0.90           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.71/0.90             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.71/0.90  thf(zf_stmt_1, axiom,
% 0.71/0.90    (![B:$i,A:$i]:
% 0.71/0.90     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.71/0.90       ( zip_tseitin_0 @ B @ A ) ))).
% 0.71/0.90  thf('8', plain,
% 0.71/0.90      (![X25 : $i, X26 : $i]:
% 0.71/0.90         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.71/0.90  thf(t113_zfmisc_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.71/0.90       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.71/0.90  thf('9', plain,
% 0.71/0.90      (![X8 : $i, X9 : $i]:
% 0.71/0.90         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.71/0.90  thf('10', plain,
% 0.71/0.90      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.71/0.90      inference('simplify', [status(thm)], ['9'])).
% 0.71/0.90  thf('11', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.71/0.90      inference('sup+', [status(thm)], ['8', '10'])).
% 0.71/0.90  thf('12', plain,
% 0.71/0.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(t3_subset, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.71/0.90  thf('13', plain,
% 0.71/0.90      (![X10 : $i, X11 : $i]:
% 0.71/0.90         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t3_subset])).
% 0.71/0.90  thf('14', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.71/0.90      inference('sup-', [status(thm)], ['12', '13'])).
% 0.71/0.90  thf('15', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((r1_tarski @ sk_D @ k1_xboole_0) | (zip_tseitin_0 @ sk_B @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['11', '14'])).
% 0.71/0.90  thf(t1_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.71/0.90       ( r1_tarski @ A @ C ) ))).
% 0.71/0.90  thf('16', plain,
% 0.71/0.90      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.71/0.90         (~ (r1_tarski @ X3 @ X4)
% 0.71/0.90          | ~ (r1_tarski @ X4 @ X5)
% 0.71/0.90          | (r1_tarski @ X3 @ X5))),
% 0.71/0.90      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.71/0.90  thf('17', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((zip_tseitin_0 @ sk_B @ X1)
% 0.71/0.90          | (r1_tarski @ sk_D @ X0)
% 0.71/0.90          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['15', '16'])).
% 0.71/0.90  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.71/0.90  thf('18', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.71/0.90      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.71/0.90  thf('19', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((zip_tseitin_0 @ sk_B @ X1) | (r1_tarski @ sk_D @ X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['17', '18'])).
% 0.71/0.90  thf('20', plain,
% 0.71/0.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.71/0.90  thf(zf_stmt_3, axiom,
% 0.71/0.90    (![C:$i,B:$i,A:$i]:
% 0.71/0.90     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.71/0.90       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.71/0.90  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.71/0.90  thf(zf_stmt_5, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.90       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.71/0.90         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.71/0.90           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.71/0.90             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.71/0.90  thf('21', plain,
% 0.71/0.90      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.71/0.90         (~ (zip_tseitin_0 @ X30 @ X31)
% 0.71/0.90          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 0.71/0.90          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.71/0.90  thf('22', plain,
% 0.71/0.90      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.71/0.90      inference('sup-', [status(thm)], ['20', '21'])).
% 0.71/0.90  thf('23', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((r1_tarski @ sk_D @ X0) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.71/0.90      inference('sup-', [status(thm)], ['19', '22'])).
% 0.71/0.90  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('25', plain,
% 0.71/0.90      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.71/0.90         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.71/0.90          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 0.71/0.90          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.71/0.90  thf('26', plain,
% 0.71/0.90      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.71/0.90        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['24', '25'])).
% 0.71/0.90  thf('27', plain,
% 0.71/0.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(redefinition_k1_relset_1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.90       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.71/0.90  thf('28', plain,
% 0.71/0.90      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.71/0.90         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.71/0.90          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.71/0.90      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.71/0.90  thf('29', plain,
% 0.71/0.90      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.71/0.90      inference('sup-', [status(thm)], ['27', '28'])).
% 0.71/0.90  thf('30', plain,
% 0.71/0.90      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.71/0.90      inference('demod', [status(thm)], ['26', '29'])).
% 0.71/0.90  thf('31', plain,
% 0.71/0.90      (![X0 : $i]: ((r1_tarski @ sk_D @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['23', '30'])).
% 0.71/0.90  thf('32', plain,
% 0.71/0.90      (![X25 : $i, X26 : $i]:
% 0.71/0.90         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.71/0.90  thf('33', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.71/0.90      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.71/0.90  thf('34', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.71/0.90      inference('sup+', [status(thm)], ['32', '33'])).
% 0.71/0.90  thf('35', plain,
% 0.71/0.90      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.71/0.90      inference('sup-', [status(thm)], ['20', '21'])).
% 0.71/0.90  thf('36', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.71/0.90      inference('sup-', [status(thm)], ['34', '35'])).
% 0.71/0.90  thf('37', plain,
% 0.71/0.90      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.71/0.90      inference('demod', [status(thm)], ['26', '29'])).
% 0.71/0.90  thf('38', plain,
% 0.71/0.90      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['36', '37'])).
% 0.71/0.90  thf(d10_xboole_0, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.71/0.90  thf('39', plain,
% 0.71/0.90      (![X0 : $i, X2 : $i]:
% 0.71/0.90         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.71/0.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.71/0.90  thf('40', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (((sk_A) = (k1_relat_1 @ sk_D))
% 0.71/0.90          | ~ (r1_tarski @ X0 @ sk_B)
% 0.71/0.90          | ((X0) = (sk_B)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['38', '39'])).
% 0.71/0.90  thf('41', plain,
% 0.71/0.90      ((((sk_A) = (k1_relat_1 @ sk_D))
% 0.71/0.90        | ((sk_D) = (sk_B))
% 0.71/0.90        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['31', '40'])).
% 0.71/0.90  thf('42', plain, ((((sk_D) = (sk_B)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.71/0.90      inference('simplify', [status(thm)], ['41'])).
% 0.71/0.90  thf(d18_relat_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( v1_relat_1 @ B ) =>
% 0.71/0.90       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.71/0.90  thf('43', plain,
% 0.71/0.90      (![X13 : $i, X14 : $i]:
% 0.71/0.90         (~ (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.71/0.90          | (v4_relat_1 @ X13 @ X14)
% 0.71/0.90          | ~ (v1_relat_1 @ X13))),
% 0.71/0.90      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.71/0.90  thf('44', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (~ (r1_tarski @ sk_A @ X0)
% 0.71/0.90          | ((sk_D) = (sk_B))
% 0.71/0.90          | ~ (v1_relat_1 @ sk_D)
% 0.71/0.90          | (v4_relat_1 @ sk_D @ X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['42', '43'])).
% 0.71/0.90  thf('45', plain,
% 0.71/0.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(cc1_relset_1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.90       ( v1_relat_1 @ C ) ))).
% 0.71/0.90  thf('46', plain,
% 0.71/0.90      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.71/0.90         ((v1_relat_1 @ X19)
% 0.71/0.90          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.71/0.90      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.71/0.90  thf('47', plain, ((v1_relat_1 @ sk_D)),
% 0.71/0.90      inference('sup-', [status(thm)], ['45', '46'])).
% 0.71/0.90  thf('48', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (~ (r1_tarski @ sk_A @ X0)
% 0.71/0.90          | ((sk_D) = (sk_B))
% 0.71/0.90          | (v4_relat_1 @ sk_D @ X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['44', '47'])).
% 0.71/0.90  thf('49', plain, (((v4_relat_1 @ sk_D @ sk_C) | ((sk_D) = (sk_B)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['7', '48'])).
% 0.71/0.90  thf(t209_relat_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.71/0.90       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.71/0.90  thf('50', plain,
% 0.71/0.90      (![X15 : $i, X16 : $i]:
% 0.71/0.90         (((X15) = (k7_relat_1 @ X15 @ X16))
% 0.71/0.90          | ~ (v4_relat_1 @ X15 @ X16)
% 0.71/0.90          | ~ (v1_relat_1 @ X15))),
% 0.71/0.90      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.71/0.90  thf('51', plain,
% 0.71/0.90      ((((sk_D) = (sk_B))
% 0.71/0.90        | ~ (v1_relat_1 @ sk_D)
% 0.71/0.90        | ((sk_D) = (k7_relat_1 @ sk_D @ sk_C)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['49', '50'])).
% 0.71/0.90  thf('52', plain, ((v1_relat_1 @ sk_D)),
% 0.71/0.90      inference('sup-', [status(thm)], ['45', '46'])).
% 0.71/0.90  thf('53', plain,
% 0.71/0.90      ((((sk_D) = (sk_B)) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_C)))),
% 0.71/0.90      inference('demod', [status(thm)], ['51', '52'])).
% 0.71/0.90  thf('54', plain,
% 0.71/0.90      (~ (r2_relset_1 @ sk_A @ sk_B @ (k7_relat_1 @ sk_D @ sk_C) @ sk_D)),
% 0.71/0.90      inference('demod', [status(thm)], ['0', '5'])).
% 0.71/0.90  thf('55', plain,
% 0.71/0.90      ((~ (r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D) | ((sk_D) = (sk_B)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['53', '54'])).
% 0.71/0.90  thf('56', plain,
% 0.71/0.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(t18_funct_2, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.71/0.90         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.71/0.90       ( ![D:$i]:
% 0.71/0.90         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.71/0.90             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.71/0.90           ( ( ![E:$i]:
% 0.71/0.90               ( ( r2_hidden @ E @ A ) =>
% 0.71/0.90                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 0.71/0.90             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 0.71/0.90  thf('57', plain,
% 0.71/0.90      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.71/0.90         (~ (v1_funct_1 @ X37)
% 0.71/0.90          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.71/0.90          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.71/0.90          | (r2_relset_1 @ X38 @ X39 @ X40 @ X37)
% 0.71/0.90          | ((k1_funct_1 @ X40 @ (sk_E @ X37 @ X40 @ X38))
% 0.71/0.90              != (k1_funct_1 @ X37 @ (sk_E @ X37 @ X40 @ X38)))
% 0.71/0.90          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.71/0.90          | ~ (v1_funct_2 @ X40 @ X38 @ X39)
% 0.71/0.90          | ~ (v1_funct_1 @ X40))),
% 0.71/0.90      inference('cnf', [status(esa)], [t18_funct_2])).
% 0.71/0.90  thf('58', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         (~ (v1_funct_1 @ X0)
% 0.71/0.90          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.71/0.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.71/0.90          | (r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.71/0.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.71/0.90          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.71/0.90          | ~ (v1_funct_1 @ X0))),
% 0.71/0.90      inference('eq_res', [status(thm)], ['57'])).
% 0.71/0.90  thf('59', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.71/0.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.71/0.90          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.71/0.90          | ~ (v1_funct_1 @ X0))),
% 0.71/0.90      inference('simplify', [status(thm)], ['58'])).
% 0.71/0.90  thf('60', plain,
% 0.71/0.90      ((~ (v1_funct_1 @ sk_D)
% 0.71/0.90        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.71/0.90        | (r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D))),
% 0.71/0.90      inference('sup-', [status(thm)], ['56', '59'])).
% 0.71/0.90  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('62', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('63', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.71/0.90      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.71/0.90  thf('64', plain, (((sk_D) = (sk_B))),
% 0.71/0.90      inference('demod', [status(thm)], ['55', '63'])).
% 0.71/0.90  thf('65', plain, (((sk_D) = (sk_B))),
% 0.71/0.90      inference('demod', [status(thm)], ['55', '63'])).
% 0.71/0.90  thf('66', plain,
% 0.71/0.90      (~ (r2_relset_1 @ sk_A @ sk_B @ (k7_relat_1 @ sk_B @ sk_C) @ sk_B)),
% 0.71/0.90      inference('demod', [status(thm)], ['6', '64', '65'])).
% 0.71/0.90  thf('67', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('68', plain,
% 0.71/0.90      (![X25 : $i, X26 : $i]:
% 0.71/0.90         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.71/0.90  thf('69', plain,
% 0.71/0.90      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.71/0.90      inference('sup-', [status(thm)], ['20', '21'])).
% 0.71/0.90  thf('70', plain,
% 0.71/0.90      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.71/0.90      inference('sup-', [status(thm)], ['68', '69'])).
% 0.71/0.90  thf('71', plain,
% 0.71/0.90      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.71/0.90      inference('demod', [status(thm)], ['26', '29'])).
% 0.71/0.90  thf('72', plain,
% 0.71/0.90      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['70', '71'])).
% 0.71/0.90  thf('73', plain,
% 0.71/0.90      (![X13 : $i, X14 : $i]:
% 0.71/0.90         (~ (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.71/0.90          | (v4_relat_1 @ X13 @ X14)
% 0.71/0.90          | ~ (v1_relat_1 @ X13))),
% 0.71/0.90      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.71/0.90  thf('74', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (~ (r1_tarski @ sk_A @ X0)
% 0.71/0.90          | ((sk_B) = (k1_xboole_0))
% 0.71/0.90          | ~ (v1_relat_1 @ sk_D)
% 0.71/0.90          | (v4_relat_1 @ sk_D @ X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['72', '73'])).
% 0.71/0.90  thf('75', plain, ((v1_relat_1 @ sk_D)),
% 0.71/0.90      inference('sup-', [status(thm)], ['45', '46'])).
% 0.71/0.90  thf('76', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (~ (r1_tarski @ sk_A @ X0)
% 0.71/0.90          | ((sk_B) = (k1_xboole_0))
% 0.71/0.90          | (v4_relat_1 @ sk_D @ X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['74', '75'])).
% 0.71/0.90  thf('77', plain, (((v4_relat_1 @ sk_D @ sk_C) | ((sk_B) = (k1_xboole_0)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['67', '76'])).
% 0.71/0.90  thf('78', plain,
% 0.71/0.90      (![X15 : $i, X16 : $i]:
% 0.71/0.90         (((X15) = (k7_relat_1 @ X15 @ X16))
% 0.71/0.90          | ~ (v4_relat_1 @ X15 @ X16)
% 0.71/0.90          | ~ (v1_relat_1 @ X15))),
% 0.71/0.90      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.71/0.90  thf('79', plain,
% 0.71/0.90      ((((sk_B) = (k1_xboole_0))
% 0.71/0.90        | ~ (v1_relat_1 @ sk_D)
% 0.71/0.90        | ((sk_D) = (k7_relat_1 @ sk_D @ sk_C)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['77', '78'])).
% 0.71/0.90  thf('80', plain, ((v1_relat_1 @ sk_D)),
% 0.71/0.90      inference('sup-', [status(thm)], ['45', '46'])).
% 0.71/0.90  thf('81', plain,
% 0.71/0.90      ((((sk_B) = (k1_xboole_0)) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_C)))),
% 0.71/0.90      inference('demod', [status(thm)], ['79', '80'])).
% 0.71/0.90  thf('82', plain,
% 0.71/0.90      (~ (r2_relset_1 @ sk_A @ sk_B @ (k7_relat_1 @ sk_D @ sk_C) @ sk_D)),
% 0.71/0.90      inference('demod', [status(thm)], ['0', '5'])).
% 0.71/0.90  thf('83', plain,
% 0.71/0.90      ((~ (r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D) | ((sk_B) = (k1_xboole_0)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['81', '82'])).
% 0.71/0.90  thf('84', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.71/0.90      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.71/0.90  thf('85', plain, (((sk_B) = (k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['83', '84'])).
% 0.71/0.90  thf('86', plain, (((sk_B) = (k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['83', '84'])).
% 0.71/0.90  thf(t88_relat_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.71/0.90  thf('87', plain,
% 0.71/0.90      (![X17 : $i, X18 : $i]:
% 0.71/0.90         ((r1_tarski @ (k7_relat_1 @ X17 @ X18) @ X17) | ~ (v1_relat_1 @ X17))),
% 0.71/0.90      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.71/0.90  thf('88', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.71/0.90      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.71/0.90  thf('89', plain,
% 0.71/0.90      (![X0 : $i, X2 : $i]:
% 0.71/0.90         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.71/0.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.71/0.90  thf('90', plain,
% 0.71/0.90      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['88', '89'])).
% 0.71/0.90  thf('91', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (~ (v1_relat_1 @ k1_xboole_0)
% 0.71/0.90          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['87', '90'])).
% 0.71/0.90  thf('92', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.71/0.90      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.71/0.90  thf('93', plain,
% 0.71/0.90      (![X10 : $i, X12 : $i]:
% 0.71/0.90         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.71/0.90      inference('cnf', [status(esa)], [t3_subset])).
% 0.71/0.90  thf('94', plain,
% 0.71/0.90      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['92', '93'])).
% 0.71/0.90  thf('95', plain,
% 0.71/0.90      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.71/0.90         ((v1_relat_1 @ X19)
% 0.71/0.90          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.71/0.90      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.71/0.90  thf('96', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.71/0.90      inference('sup-', [status(thm)], ['94', '95'])).
% 0.71/0.90  thf('97', plain,
% 0.71/0.90      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['91', '96'])).
% 0.71/0.90  thf('98', plain, (((sk_B) = (k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['83', '84'])).
% 0.71/0.90  thf('99', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.71/0.90      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.71/0.90  thf('100', plain, (((sk_D) = (sk_B))),
% 0.71/0.90      inference('demod', [status(thm)], ['55', '63'])).
% 0.71/0.90  thf('101', plain, (((sk_D) = (sk_B))),
% 0.71/0.90      inference('demod', [status(thm)], ['55', '63'])).
% 0.71/0.90  thf('102', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 0.71/0.90      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.71/0.90  thf('103', plain, (((sk_B) = (k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['83', '84'])).
% 0.71/0.90  thf('104', plain, (((sk_B) = (k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['83', '84'])).
% 0.71/0.90  thf('105', plain, (((sk_B) = (k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['83', '84'])).
% 0.71/0.90  thf('106', plain,
% 0.71/0.90      ((r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.71/0.90      inference('demod', [status(thm)], ['102', '103', '104', '105'])).
% 0.71/0.90  thf('107', plain, ($false),
% 0.71/0.90      inference('demod', [status(thm)], ['66', '85', '86', '97', '98', '106'])).
% 0.71/0.90  
% 0.71/0.90  % SZS output end Refutation
% 0.71/0.90  
% 0.71/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

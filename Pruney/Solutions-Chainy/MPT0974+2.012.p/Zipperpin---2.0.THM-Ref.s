%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AshcXoDoHa

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:41 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 145 expanded)
%              Number of leaves         :   37 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  869 (2863 expanded)
%              Number of equality atoms :   61 ( 215 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf(t20_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ D )
                = B )
              & ( ( k2_relset_1 @ B @ C @ E )
                = C ) )
           => ( ( C = k1_xboole_0 )
              | ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                = C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ B @ C )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ D )
                  = B )
                & ( ( k2_relset_1 @ B @ C @ E )
                  = C ) )
             => ( ( C = k1_xboole_0 )
                | ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                  = C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_funct_2])).

thf('1',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
 != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 )
        = ( k5_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
 != sk_C ),
    inference(demod,[status(thm)],['1','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X7 @ X8 @ X10 @ X11 @ X6 @ X9 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k4_relset_1 @ X19 @ X20 @ X22 @ X23 @ X18 @ X21 )
        = ( k5_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('24',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
 != sk_C ),
    inference(demod,[status(thm)],['11','24'])).

thf('26',plain,
    ( ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
     != sk_C )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('29',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
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

thf('33',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('36',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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

thf('37',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('38',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('44',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['34','41','44'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('47',plain,
    ( ( ( k9_relat_1 @ sk_E @ sk_B )
      = ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('50',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k2_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('54',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('55',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k9_relat_1 @ sk_E @ sk_B )
    = sk_C ),
    inference(demod,[status(thm)],['47','52','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('59',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['53','54'])).

thf('61',plain,(
    sk_C != sk_C ),
    inference(demod,[status(thm)],['26','31','56','59','60'])).

thf('62',plain,(
    $false ),
    inference(simplify,[status(thm)],['61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AshcXoDoHa
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:45:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.51/1.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.51/1.71  % Solved by: fo/fo7.sh
% 1.51/1.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.51/1.71  % done 553 iterations in 1.275s
% 1.51/1.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.51/1.71  % SZS output start Refutation
% 1.51/1.71  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.51/1.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.51/1.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.51/1.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.51/1.71  thf(sk_D_type, type, sk_D: $i).
% 1.51/1.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.51/1.71  thf(sk_E_type, type, sk_E: $i).
% 1.51/1.71  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.51/1.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.51/1.71  thf(sk_B_type, type, sk_B: $i).
% 1.51/1.71  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 1.51/1.71  thf(sk_C_type, type, sk_C: $i).
% 1.51/1.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.51/1.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.51/1.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.51/1.71  thf(sk_A_type, type, sk_A: $i).
% 1.51/1.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.51/1.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.51/1.71  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.51/1.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.51/1.71  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.51/1.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.51/1.71  thf(t160_relat_1, axiom,
% 1.51/1.71    (![A:$i]:
% 1.51/1.71     ( ( v1_relat_1 @ A ) =>
% 1.51/1.71       ( ![B:$i]:
% 1.51/1.71         ( ( v1_relat_1 @ B ) =>
% 1.51/1.71           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.51/1.71             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.51/1.71  thf('0', plain,
% 1.51/1.71      (![X1 : $i, X2 : $i]:
% 1.51/1.71         (~ (v1_relat_1 @ X1)
% 1.51/1.71          | ((k2_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 1.51/1.71              = (k9_relat_1 @ X1 @ (k2_relat_1 @ X2)))
% 1.51/1.71          | ~ (v1_relat_1 @ X2))),
% 1.51/1.71      inference('cnf', [status(esa)], [t160_relat_1])).
% 1.51/1.71  thf(t20_funct_2, conjecture,
% 1.51/1.71    (![A:$i,B:$i,C:$i,D:$i]:
% 1.51/1.71     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.51/1.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.51/1.71       ( ![E:$i]:
% 1.51/1.71         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.51/1.71             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.51/1.71           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.51/1.71               ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 1.51/1.71             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.51/1.71               ( ( k2_relset_1 @
% 1.51/1.71                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.51/1.71                 ( C ) ) ) ) ) ) ))).
% 1.51/1.71  thf(zf_stmt_0, negated_conjecture,
% 1.51/1.71    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.51/1.71        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.51/1.71            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.51/1.71          ( ![E:$i]:
% 1.51/1.71            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.51/1.71                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.51/1.71              ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.51/1.71                  ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 1.51/1.71                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.51/1.71                  ( ( k2_relset_1 @
% 1.51/1.71                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.51/1.71                    ( C ) ) ) ) ) ) ) )),
% 1.51/1.71    inference('cnf.neg', [status(esa)], [t20_funct_2])).
% 1.51/1.71  thf('1', plain,
% 1.51/1.71      (((k2_relset_1 @ sk_A @ sk_C @ 
% 1.51/1.71         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) != (sk_C))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('2', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('3', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf(redefinition_k1_partfun1, axiom,
% 1.51/1.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.51/1.71     ( ( ( v1_funct_1 @ E ) & 
% 1.51/1.71         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.51/1.71         ( v1_funct_1 @ F ) & 
% 1.51/1.71         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.51/1.71       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.51/1.71  thf('4', plain,
% 1.51/1.71      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.51/1.71         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.51/1.71          | ~ (v1_funct_1 @ X32)
% 1.51/1.71          | ~ (v1_funct_1 @ X35)
% 1.51/1.71          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.51/1.71          | ((k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35)
% 1.51/1.71              = (k5_relat_1 @ X32 @ X35)))),
% 1.51/1.71      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.51/1.71  thf('5', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.71         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.51/1.71            = (k5_relat_1 @ sk_D @ X0))
% 1.51/1.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.51/1.71          | ~ (v1_funct_1 @ X0)
% 1.51/1.71          | ~ (v1_funct_1 @ sk_D))),
% 1.51/1.71      inference('sup-', [status(thm)], ['3', '4'])).
% 1.51/1.71  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('7', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.71         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.51/1.72            = (k5_relat_1 @ sk_D @ X0))
% 1.51/1.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.51/1.72          | ~ (v1_funct_1 @ X0))),
% 1.51/1.72      inference('demod', [status(thm)], ['5', '6'])).
% 1.51/1.72  thf('8', plain,
% 1.51/1.72      ((~ (v1_funct_1 @ sk_E)
% 1.51/1.72        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.51/1.72            = (k5_relat_1 @ sk_D @ sk_E)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['2', '7'])).
% 1.51/1.72  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('10', plain,
% 1.51/1.72      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.51/1.72         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.51/1.72      inference('demod', [status(thm)], ['8', '9'])).
% 1.51/1.72  thf('11', plain,
% 1.51/1.72      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) != (sk_C))),
% 1.51/1.72      inference('demod', [status(thm)], ['1', '10'])).
% 1.51/1.72  thf('12', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('13', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf(dt_k4_relset_1, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.51/1.72     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.51/1.72         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.51/1.72       ( m1_subset_1 @
% 1.51/1.72         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.51/1.72         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 1.51/1.72  thf('14', plain,
% 1.51/1.72      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.51/1.72         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 1.51/1.72          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 1.51/1.72          | (m1_subset_1 @ (k4_relset_1 @ X7 @ X8 @ X10 @ X11 @ X6 @ X9) @ 
% 1.51/1.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X11))))),
% 1.51/1.72      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 1.51/1.72  thf('15', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.72         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 1.51/1.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.51/1.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 1.51/1.72      inference('sup-', [status(thm)], ['13', '14'])).
% 1.51/1.72  thf('16', plain,
% 1.51/1.72      ((m1_subset_1 @ 
% 1.51/1.72        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 1.51/1.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['12', '15'])).
% 1.51/1.72  thf('17', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('18', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf(redefinition_k4_relset_1, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.51/1.72     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.51/1.72         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.51/1.72       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.51/1.72  thf('19', plain,
% 1.51/1.72      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.51/1.72         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.51/1.72          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.51/1.72          | ((k4_relset_1 @ X19 @ X20 @ X22 @ X23 @ X18 @ X21)
% 1.51/1.72              = (k5_relat_1 @ X18 @ X21)))),
% 1.51/1.72      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 1.51/1.72  thf('20', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.72         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.51/1.72            = (k5_relat_1 @ sk_D @ X0))
% 1.51/1.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.51/1.72      inference('sup-', [status(thm)], ['18', '19'])).
% 1.51/1.72  thf('21', plain,
% 1.51/1.72      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.51/1.72         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.51/1.72      inference('sup-', [status(thm)], ['17', '20'])).
% 1.51/1.72  thf('22', plain,
% 1.51/1.72      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 1.51/1.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.51/1.72      inference('demod', [status(thm)], ['16', '21'])).
% 1.51/1.72  thf(redefinition_k2_relset_1, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i]:
% 1.51/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.72       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.51/1.72  thf('23', plain,
% 1.51/1.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.51/1.72         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 1.51/1.72          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.51/1.72      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.51/1.72  thf('24', plain,
% 1.51/1.72      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 1.51/1.72         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['22', '23'])).
% 1.51/1.72  thf('25', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) != (sk_C))),
% 1.51/1.72      inference('demod', [status(thm)], ['11', '24'])).
% 1.51/1.72  thf('26', plain,
% 1.51/1.72      ((((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) != (sk_C))
% 1.51/1.72        | ~ (v1_relat_1 @ sk_D)
% 1.51/1.72        | ~ (v1_relat_1 @ sk_E))),
% 1.51/1.72      inference('sup-', [status(thm)], ['0', '25'])).
% 1.51/1.72  thf('27', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('28', plain,
% 1.51/1.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.51/1.72         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 1.51/1.72          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.51/1.72      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.51/1.72  thf('29', plain,
% 1.51/1.72      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.51/1.72      inference('sup-', [status(thm)], ['27', '28'])).
% 1.51/1.72  thf('30', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_B))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('31', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 1.51/1.72      inference('sup+', [status(thm)], ['29', '30'])).
% 1.51/1.72  thf('32', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf(d1_funct_2, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i]:
% 1.51/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.51/1.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.51/1.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.51/1.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.51/1.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.51/1.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.51/1.72  thf(zf_stmt_1, axiom,
% 1.51/1.72    (![C:$i,B:$i,A:$i]:
% 1.51/1.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.51/1.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.51/1.72  thf('33', plain,
% 1.51/1.72      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.51/1.72         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 1.51/1.72          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 1.51/1.72          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.51/1.72  thf('34', plain,
% 1.51/1.72      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 1.51/1.72        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['32', '33'])).
% 1.51/1.72  thf(zf_stmt_2, axiom,
% 1.51/1.72    (![B:$i,A:$i]:
% 1.51/1.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.51/1.72       ( zip_tseitin_0 @ B @ A ) ))).
% 1.51/1.72  thf('35', plain,
% 1.51/1.72      (![X24 : $i, X25 : $i]:
% 1.51/1.72         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.51/1.72  thf('36', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.51/1.72  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.51/1.72  thf(zf_stmt_5, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i]:
% 1.51/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.51/1.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.51/1.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.51/1.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.51/1.72  thf('37', plain,
% 1.51/1.72      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.51/1.72         (~ (zip_tseitin_0 @ X29 @ X30)
% 1.51/1.72          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 1.51/1.72          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.51/1.72  thf('38', plain,
% 1.51/1.72      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.51/1.72      inference('sup-', [status(thm)], ['36', '37'])).
% 1.51/1.72  thf('39', plain,
% 1.51/1.72      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 1.51/1.72      inference('sup-', [status(thm)], ['35', '38'])).
% 1.51/1.72  thf('40', plain, (((sk_C) != (k1_xboole_0))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('41', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 1.51/1.72      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 1.51/1.72  thf('42', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf(redefinition_k1_relset_1, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i]:
% 1.51/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.51/1.72  thf('43', plain,
% 1.51/1.72      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.51/1.72         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 1.51/1.72          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.51/1.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.51/1.72  thf('44', plain,
% 1.51/1.72      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.51/1.72      inference('sup-', [status(thm)], ['42', '43'])).
% 1.51/1.72  thf('45', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 1.51/1.72      inference('demod', [status(thm)], ['34', '41', '44'])).
% 1.51/1.72  thf(t146_relat_1, axiom,
% 1.51/1.72    (![A:$i]:
% 1.51/1.72     ( ( v1_relat_1 @ A ) =>
% 1.51/1.72       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 1.51/1.72  thf('46', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 1.51/1.72          | ~ (v1_relat_1 @ X0))),
% 1.51/1.72      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.51/1.72  thf('47', plain,
% 1.51/1.72      ((((k9_relat_1 @ sk_E @ sk_B) = (k2_relat_1 @ sk_E))
% 1.51/1.72        | ~ (v1_relat_1 @ sk_E))),
% 1.51/1.72      inference('sup+', [status(thm)], ['45', '46'])).
% 1.51/1.72  thf('48', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('49', plain,
% 1.51/1.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.51/1.72         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 1.51/1.72          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.51/1.72      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.51/1.72  thf('50', plain,
% 1.51/1.72      (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (k2_relat_1 @ sk_E))),
% 1.51/1.72      inference('sup-', [status(thm)], ['48', '49'])).
% 1.51/1.72  thf('51', plain, (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (sk_C))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('52', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 1.51/1.72      inference('sup+', [status(thm)], ['50', '51'])).
% 1.51/1.72  thf('53', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf(cc1_relset_1, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i]:
% 1.51/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.72       ( v1_relat_1 @ C ) ))).
% 1.51/1.72  thf('54', plain,
% 1.51/1.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.51/1.72         ((v1_relat_1 @ X3)
% 1.51/1.72          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 1.51/1.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.51/1.72  thf('55', plain, ((v1_relat_1 @ sk_E)),
% 1.51/1.72      inference('sup-', [status(thm)], ['53', '54'])).
% 1.51/1.72  thf('56', plain, (((k9_relat_1 @ sk_E @ sk_B) = (sk_C))),
% 1.51/1.72      inference('demod', [status(thm)], ['47', '52', '55'])).
% 1.51/1.72  thf('57', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('58', plain,
% 1.51/1.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.51/1.72         ((v1_relat_1 @ X3)
% 1.51/1.72          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 1.51/1.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.51/1.72  thf('59', plain, ((v1_relat_1 @ sk_D)),
% 1.51/1.72      inference('sup-', [status(thm)], ['57', '58'])).
% 1.51/1.72  thf('60', plain, ((v1_relat_1 @ sk_E)),
% 1.51/1.72      inference('sup-', [status(thm)], ['53', '54'])).
% 1.51/1.72  thf('61', plain, (((sk_C) != (sk_C))),
% 1.51/1.72      inference('demod', [status(thm)], ['26', '31', '56', '59', '60'])).
% 1.51/1.72  thf('62', plain, ($false), inference('simplify', [status(thm)], ['61'])).
% 1.51/1.72  
% 1.51/1.72  % SZS output end Refutation
% 1.51/1.72  
% 1.51/1.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

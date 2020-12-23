%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MTU25UKmeU

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:43 EST 2020

% Result     : Theorem 1.70s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 154 expanded)
%              Number of leaves         :   38 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  893 (2905 expanded)
%              Number of equality atoms :   61 ( 215 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k9_relat_1 @ X5 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 )
        = ( k5_relat_1 @ X33 @ X36 ) ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X8 @ X9 @ X11 @ X12 @ X7 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X12 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k4_relset_1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22 )
        = ( k5_relat_1 @ X19 @ X22 ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    ! [X4: $i] :
      ( ( ( k9_relat_1 @ X4 @ ( k1_relat_1 @ X4 ) )
        = ( k2_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('57',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k9_relat_1 @ sk_E @ sk_B )
    = sk_C ),
    inference(demod,[status(thm)],['47','52','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('63',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['55','56'])).

thf('65',plain,(
    sk_C != sk_C ),
    inference(demod,[status(thm)],['26','31','58','63','64'])).

thf('66',plain,(
    $false ),
    inference(simplify,[status(thm)],['65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MTU25UKmeU
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:11:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.70/1.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.70/1.90  % Solved by: fo/fo7.sh
% 1.70/1.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.70/1.90  % done 633 iterations in 1.417s
% 1.70/1.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.70/1.90  % SZS output start Refutation
% 1.70/1.90  thf(sk_E_type, type, sk_E: $i).
% 1.70/1.90  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.70/1.90  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.70/1.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.70/1.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.70/1.90  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.70/1.90  thf(sk_D_type, type, sk_D: $i).
% 1.70/1.90  thf(sk_A_type, type, sk_A: $i).
% 1.70/1.90  thf(sk_C_type, type, sk_C: $i).
% 1.70/1.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.70/1.90  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.70/1.90  thf(sk_B_type, type, sk_B: $i).
% 1.70/1.90  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.70/1.90  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.70/1.90  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.70/1.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.70/1.90  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.70/1.90  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.70/1.90  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 1.70/1.90  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.70/1.90  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.70/1.90  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.70/1.90  thf(t160_relat_1, axiom,
% 1.70/1.90    (![A:$i]:
% 1.70/1.90     ( ( v1_relat_1 @ A ) =>
% 1.70/1.90       ( ![B:$i]:
% 1.70/1.90         ( ( v1_relat_1 @ B ) =>
% 1.70/1.90           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.70/1.90             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.70/1.90  thf('0', plain,
% 1.70/1.90      (![X5 : $i, X6 : $i]:
% 1.70/1.90         (~ (v1_relat_1 @ X5)
% 1.70/1.90          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 1.70/1.90              = (k9_relat_1 @ X5 @ (k2_relat_1 @ X6)))
% 1.70/1.90          | ~ (v1_relat_1 @ X6))),
% 1.70/1.90      inference('cnf', [status(esa)], [t160_relat_1])).
% 1.70/1.90  thf(t20_funct_2, conjecture,
% 1.70/1.90    (![A:$i,B:$i,C:$i,D:$i]:
% 1.70/1.90     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.70/1.90         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.70/1.90       ( ![E:$i]:
% 1.70/1.90         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.70/1.90             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.70/1.90           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.70/1.90               ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 1.70/1.90             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.70/1.90               ( ( k2_relset_1 @
% 1.70/1.90                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.70/1.90                 ( C ) ) ) ) ) ) ))).
% 1.70/1.90  thf(zf_stmt_0, negated_conjecture,
% 1.70/1.90    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.70/1.90        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.70/1.90            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.70/1.90          ( ![E:$i]:
% 1.70/1.90            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.70/1.90                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.70/1.90              ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.70/1.90                  ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 1.70/1.90                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.70/1.90                  ( ( k2_relset_1 @
% 1.70/1.90                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.70/1.90                    ( C ) ) ) ) ) ) ) )),
% 1.70/1.90    inference('cnf.neg', [status(esa)], [t20_funct_2])).
% 1.70/1.90  thf('1', plain,
% 1.70/1.90      (((k2_relset_1 @ sk_A @ sk_C @ 
% 1.70/1.90         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) != (sk_C))),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.70/1.90  thf('2', plain,
% 1.70/1.90      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.70/1.90  thf('3', plain,
% 1.70/1.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.70/1.90  thf(redefinition_k1_partfun1, axiom,
% 1.70/1.90    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.70/1.90     ( ( ( v1_funct_1 @ E ) & 
% 1.70/1.90         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.70/1.90         ( v1_funct_1 @ F ) & 
% 1.70/1.90         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.70/1.90       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.70/1.90  thf('4', plain,
% 1.70/1.90      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.70/1.90         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.70/1.90          | ~ (v1_funct_1 @ X33)
% 1.70/1.90          | ~ (v1_funct_1 @ X36)
% 1.70/1.90          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.70/1.90          | ((k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36)
% 1.70/1.90              = (k5_relat_1 @ X33 @ X36)))),
% 1.70/1.90      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.70/1.90  thf('5', plain,
% 1.70/1.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.70/1.90         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.70/1.90            = (k5_relat_1 @ sk_D @ X0))
% 1.70/1.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.70/1.90          | ~ (v1_funct_1 @ X0)
% 1.70/1.90          | ~ (v1_funct_1 @ sk_D))),
% 1.70/1.90      inference('sup-', [status(thm)], ['3', '4'])).
% 1.70/1.90  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.70/1.90  thf('7', plain,
% 1.70/1.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.70/1.90         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.70/1.90            = (k5_relat_1 @ sk_D @ X0))
% 1.70/1.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.70/1.90          | ~ (v1_funct_1 @ X0))),
% 1.70/1.90      inference('demod', [status(thm)], ['5', '6'])).
% 1.70/1.90  thf('8', plain,
% 1.70/1.90      ((~ (v1_funct_1 @ sk_E)
% 1.70/1.90        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.70/1.90            = (k5_relat_1 @ sk_D @ sk_E)))),
% 1.70/1.90      inference('sup-', [status(thm)], ['2', '7'])).
% 1.70/1.90  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.70/1.90  thf('10', plain,
% 1.70/1.90      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.70/1.90         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.70/1.90      inference('demod', [status(thm)], ['8', '9'])).
% 1.70/1.90  thf('11', plain,
% 1.70/1.90      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) != (sk_C))),
% 1.70/1.90      inference('demod', [status(thm)], ['1', '10'])).
% 1.70/1.90  thf('12', plain,
% 1.70/1.90      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.70/1.90  thf('13', plain,
% 1.70/1.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.70/1.90  thf(dt_k4_relset_1, axiom,
% 1.70/1.90    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.70/1.90     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.70/1.90         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.70/1.90       ( m1_subset_1 @
% 1.70/1.90         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.70/1.90         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 1.70/1.90  thf('14', plain,
% 1.70/1.90      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.70/1.90         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 1.70/1.90          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 1.70/1.90          | (m1_subset_1 @ (k4_relset_1 @ X8 @ X9 @ X11 @ X12 @ X7 @ X10) @ 
% 1.70/1.90             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X12))))),
% 1.70/1.90      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 1.70/1.90  thf('15', plain,
% 1.70/1.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.70/1.90         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 1.70/1.90           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.70/1.90          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 1.70/1.90      inference('sup-', [status(thm)], ['13', '14'])).
% 1.70/1.90  thf('16', plain,
% 1.70/1.90      ((m1_subset_1 @ 
% 1.70/1.90        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 1.70/1.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.70/1.90      inference('sup-', [status(thm)], ['12', '15'])).
% 1.70/1.90  thf('17', plain,
% 1.70/1.90      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.70/1.90  thf('18', plain,
% 1.70/1.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.70/1.90  thf(redefinition_k4_relset_1, axiom,
% 1.70/1.90    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.70/1.90     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.70/1.90         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.70/1.90       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.70/1.90  thf('19', plain,
% 1.70/1.90      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.70/1.90         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.70/1.90          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.70/1.90          | ((k4_relset_1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22)
% 1.70/1.90              = (k5_relat_1 @ X19 @ X22)))),
% 1.70/1.90      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 1.70/1.90  thf('20', plain,
% 1.70/1.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.70/1.90         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.70/1.90            = (k5_relat_1 @ sk_D @ X0))
% 1.70/1.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.70/1.90      inference('sup-', [status(thm)], ['18', '19'])).
% 1.70/1.90  thf('21', plain,
% 1.70/1.90      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.70/1.90         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.70/1.90      inference('sup-', [status(thm)], ['17', '20'])).
% 1.70/1.90  thf('22', plain,
% 1.70/1.90      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 1.70/1.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.70/1.90      inference('demod', [status(thm)], ['16', '21'])).
% 1.70/1.90  thf(redefinition_k2_relset_1, axiom,
% 1.70/1.90    (![A:$i,B:$i,C:$i]:
% 1.70/1.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.70/1.90       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.70/1.90  thf('23', plain,
% 1.70/1.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.70/1.90         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 1.70/1.90          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.70/1.90      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.70/1.90  thf('24', plain,
% 1.70/1.90      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 1.70/1.90         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 1.70/1.90      inference('sup-', [status(thm)], ['22', '23'])).
% 1.70/1.90  thf('25', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) != (sk_C))),
% 1.70/1.90      inference('demod', [status(thm)], ['11', '24'])).
% 1.70/1.90  thf('26', plain,
% 1.70/1.90      ((((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) != (sk_C))
% 1.70/1.90        | ~ (v1_relat_1 @ sk_D)
% 1.70/1.90        | ~ (v1_relat_1 @ sk_E))),
% 1.70/1.90      inference('sup-', [status(thm)], ['0', '25'])).
% 1.70/1.90  thf('27', plain,
% 1.70/1.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.70/1.90  thf('28', plain,
% 1.70/1.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.70/1.90         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 1.70/1.90          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.70/1.90      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.70/1.90  thf('29', plain,
% 1.70/1.90      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.70/1.90      inference('sup-', [status(thm)], ['27', '28'])).
% 1.70/1.90  thf('30', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_B))),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.70/1.90  thf('31', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 1.70/1.90      inference('sup+', [status(thm)], ['29', '30'])).
% 1.70/1.90  thf('32', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.70/1.90  thf(d1_funct_2, axiom,
% 1.70/1.90    (![A:$i,B:$i,C:$i]:
% 1.70/1.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.70/1.90       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.70/1.90           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.70/1.90             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.70/1.90         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.70/1.90           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.70/1.90             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.70/1.90  thf(zf_stmt_1, axiom,
% 1.70/1.90    (![C:$i,B:$i,A:$i]:
% 1.70/1.90     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.70/1.90       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.70/1.90  thf('33', plain,
% 1.70/1.90      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.70/1.90         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 1.70/1.90          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 1.70/1.90          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.70/1.90  thf('34', plain,
% 1.70/1.90      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 1.70/1.90        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 1.70/1.90      inference('sup-', [status(thm)], ['32', '33'])).
% 1.70/1.90  thf(zf_stmt_2, axiom,
% 1.70/1.90    (![B:$i,A:$i]:
% 1.70/1.90     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.70/1.90       ( zip_tseitin_0 @ B @ A ) ))).
% 1.70/1.90  thf('35', plain,
% 1.70/1.90      (![X25 : $i, X26 : $i]:
% 1.70/1.90         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.70/1.90  thf('36', plain,
% 1.70/1.90      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.70/1.90  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.70/1.90  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.70/1.90  thf(zf_stmt_5, axiom,
% 1.70/1.90    (![A:$i,B:$i,C:$i]:
% 1.70/1.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.70/1.90       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.70/1.90         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.70/1.90           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.70/1.90             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.70/1.90  thf('37', plain,
% 1.70/1.90      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.70/1.90         (~ (zip_tseitin_0 @ X30 @ X31)
% 1.70/1.90          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 1.70/1.90          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.70/1.90  thf('38', plain,
% 1.70/1.90      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.70/1.90      inference('sup-', [status(thm)], ['36', '37'])).
% 1.70/1.90  thf('39', plain,
% 1.70/1.90      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 1.70/1.90      inference('sup-', [status(thm)], ['35', '38'])).
% 1.70/1.90  thf('40', plain, (((sk_C) != (k1_xboole_0))),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.70/1.90  thf('41', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 1.70/1.90      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 1.70/1.90  thf('42', plain,
% 1.70/1.90      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.70/1.90  thf(redefinition_k1_relset_1, axiom,
% 1.70/1.90    (![A:$i,B:$i,C:$i]:
% 1.70/1.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.70/1.90       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.70/1.90  thf('43', plain,
% 1.70/1.90      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.70/1.90         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 1.70/1.90          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.70/1.90      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.70/1.90  thf('44', plain,
% 1.70/1.90      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.70/1.90      inference('sup-', [status(thm)], ['42', '43'])).
% 1.70/1.90  thf('45', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 1.70/1.90      inference('demod', [status(thm)], ['34', '41', '44'])).
% 1.70/1.90  thf(t146_relat_1, axiom,
% 1.70/1.90    (![A:$i]:
% 1.70/1.90     ( ( v1_relat_1 @ A ) =>
% 1.70/1.90       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 1.70/1.90  thf('46', plain,
% 1.70/1.90      (![X4 : $i]:
% 1.70/1.90         (((k9_relat_1 @ X4 @ (k1_relat_1 @ X4)) = (k2_relat_1 @ X4))
% 1.70/1.90          | ~ (v1_relat_1 @ X4))),
% 1.70/1.90      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.70/1.90  thf('47', plain,
% 1.70/1.90      ((((k9_relat_1 @ sk_E @ sk_B) = (k2_relat_1 @ sk_E))
% 1.70/1.90        | ~ (v1_relat_1 @ sk_E))),
% 1.70/1.90      inference('sup+', [status(thm)], ['45', '46'])).
% 1.70/1.90  thf('48', plain,
% 1.70/1.90      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.70/1.90  thf('49', plain,
% 1.70/1.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.70/1.90         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 1.70/1.90          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.70/1.90      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.70/1.90  thf('50', plain,
% 1.70/1.90      (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (k2_relat_1 @ sk_E))),
% 1.70/1.90      inference('sup-', [status(thm)], ['48', '49'])).
% 1.70/1.90  thf('51', plain, (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (sk_C))),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.70/1.90  thf('52', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 1.70/1.90      inference('sup+', [status(thm)], ['50', '51'])).
% 1.70/1.90  thf('53', plain,
% 1.70/1.90      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.70/1.90  thf(cc2_relat_1, axiom,
% 1.70/1.90    (![A:$i]:
% 1.70/1.90     ( ( v1_relat_1 @ A ) =>
% 1.70/1.90       ( ![B:$i]:
% 1.70/1.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.70/1.90  thf('54', plain,
% 1.70/1.90      (![X0 : $i, X1 : $i]:
% 1.70/1.90         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.70/1.90          | (v1_relat_1 @ X0)
% 1.70/1.90          | ~ (v1_relat_1 @ X1))),
% 1.70/1.90      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.70/1.90  thf('55', plain,
% 1.70/1.90      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_E))),
% 1.70/1.90      inference('sup-', [status(thm)], ['53', '54'])).
% 1.70/1.90  thf(fc6_relat_1, axiom,
% 1.70/1.90    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.70/1.90  thf('56', plain,
% 1.70/1.90      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.70/1.90      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.70/1.90  thf('57', plain, ((v1_relat_1 @ sk_E)),
% 1.70/1.90      inference('demod', [status(thm)], ['55', '56'])).
% 1.70/1.90  thf('58', plain, (((k9_relat_1 @ sk_E @ sk_B) = (sk_C))),
% 1.70/1.90      inference('demod', [status(thm)], ['47', '52', '57'])).
% 1.70/1.90  thf('59', plain,
% 1.70/1.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.70/1.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.70/1.90  thf('60', plain,
% 1.70/1.90      (![X0 : $i, X1 : $i]:
% 1.70/1.90         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.70/1.90          | (v1_relat_1 @ X0)
% 1.70/1.90          | ~ (v1_relat_1 @ X1))),
% 1.70/1.90      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.70/1.90  thf('61', plain,
% 1.70/1.90      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 1.70/1.90      inference('sup-', [status(thm)], ['59', '60'])).
% 1.70/1.90  thf('62', plain,
% 1.70/1.90      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.70/1.90      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.70/1.90  thf('63', plain, ((v1_relat_1 @ sk_D)),
% 1.70/1.90      inference('demod', [status(thm)], ['61', '62'])).
% 1.70/1.90  thf('64', plain, ((v1_relat_1 @ sk_E)),
% 1.70/1.90      inference('demod', [status(thm)], ['55', '56'])).
% 1.70/1.90  thf('65', plain, (((sk_C) != (sk_C))),
% 1.70/1.90      inference('demod', [status(thm)], ['26', '31', '58', '63', '64'])).
% 1.70/1.90  thf('66', plain, ($false), inference('simplify', [status(thm)], ['65'])).
% 1.70/1.90  
% 1.70/1.90  % SZS output end Refutation
% 1.70/1.90  
% 1.70/1.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fcwNCK3kzq

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:01 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  223 ( 426 expanded)
%              Number of leaves         :   64 ( 154 expanded)
%              Depth                    :   32
%              Number of atoms          : 1988 (7771 expanded)
%              Number of equality atoms :   96 ( 314 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t186_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ! [E: $i] :
              ( ( ( v1_funct_1 @ E )
                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                   => ( ( B = k1_xboole_0 )
                      | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                        = ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( v1_xboole_0 @ C )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ! [E: $i] :
                ( ( ( v1_funct_1 @ E )
                  & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
               => ! [F: $i] :
                    ( ( m1_subset_1 @ F @ B )
                   => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                     => ( ( B = k1_xboole_0 )
                        | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                          = ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t186_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc6_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ~ ( v1_xboole_0 @ C )
              & ( v1_funct_2 @ C @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X39 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc6_funct_2])).

thf('2',plain,
    ( ~ ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( v1_xboole_0 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
    | ( v1_xboole_0 @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X34 @ X32 )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) )
    | ( v1_xboole_0 @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k2_relset_1 @ X36 @ X37 @ X35 )
        = ( k2_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v5_relat_1 @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('23',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('29',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('31',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
            & ( v1_funct_2 @ D @ A @ C )
            & ( v1_funct_1 @ D ) )
          | ( ( A != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( A != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_2 @ D @ C @ A )
     => ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( zip_tseitin_3 @ B @ A )
          | ( zip_tseitin_2 @ D @ C @ A ) ) ) ) )).

thf('33',plain,(
    ! [X69: $i,X70: $i,X71: $i,X72: $i] :
      ( ( zip_tseitin_3 @ X69 @ X70 )
      | ~ ( v1_funct_1 @ X71 )
      | ~ ( v1_funct_2 @ X71 @ X70 @ X69 )
      | ~ ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X70 @ X69 ) ) )
      | ( zip_tseitin_2 @ X71 @ X72 @ X70 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X70 @ X69 @ X71 ) @ X72 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) @ X0 )
      | ( zip_tseitin_2 @ sk_D_1 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( zip_tseitin_3 @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('36',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 )
      | ( zip_tseitin_2 @ sk_D_1 @ X0 @ sk_B_1 )
      | ( zip_tseitin_3 @ sk_C @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,
    ( ( zip_tseitin_3 @ sk_C @ sk_B_1 )
    | ( zip_tseitin_2 @ sk_D_1 @ ( k1_relat_1 @ sk_E ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ( v1_funct_2 @ X64 @ X66 @ X65 )
      | ~ ( zip_tseitin_2 @ X64 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('41',plain,
    ( ( zip_tseitin_3 @ sk_C @ sk_B_1 )
    | ( v1_funct_2 @ sk_D_1 @ sk_B_1 @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( zip_tseitin_3 @ sk_C @ sk_B_1 )
    | ( zip_tseitin_2 @ sk_D_1 @ ( k1_relat_1 @ sk_E ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('43',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X65 ) ) )
      | ~ ( zip_tseitin_2 @ X64 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('44',plain,
    ( ( zip_tseitin_3 @ sk_C @ sk_B_1 )
    | ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k1_relat_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('45',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ~ ( r2_hidden @ X60 @ X61 )
      | ( X62 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X63 )
      | ~ ( v1_funct_2 @ X63 @ X61 @ X62 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X62 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X63 @ X60 ) @ X62 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_C @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B_1 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_C @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B_1 @ ( k1_relat_1 @ sk_E ) )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_C @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( zip_tseitin_3 @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( zip_tseitin_3 @ sk_C @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_3 @ sk_C @ sk_B_1 )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['26','50'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('52',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X41 @ ( k1_relat_1 @ X42 ) )
      | ( ( k7_partfun1 @ X43 @ X42 @ X41 )
        = ( k1_funct_1 @ X42 @ X41 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v5_relat_1 @ X42 @ X43 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( zip_tseitin_3 @ sk_C @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('55',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('56',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( zip_tseitin_3 @ sk_C @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['53','56','57'])).

thf('59',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_3 @ sk_C @ sk_B_1 )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','58'])).

thf('60',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D_1 @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('63',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t185_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ! [E: $i] :
              ( ( ( v1_funct_1 @ E )
                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                   => ( ( B = k1_xboole_0 )
                      | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                        = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )).

thf('64',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X47 @ X45 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X45 @ X46 @ X49 @ X44 @ X48 ) @ X47 )
        = ( k1_funct_1 @ X48 @ ( k1_funct_1 @ X44 @ X47 ) ) )
      | ( X45 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X45 @ X46 @ X44 ) @ ( k1_relset_1 @ X46 @ X49 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X49 ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C @ X1 @ sk_D_1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_1 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('67',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C @ X1 @ sk_D_1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_1 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C @ X1 @ sk_D_1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_1 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D_1 @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','71'])).

thf('73',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('74',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D_1 @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D_1 @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D_1 @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['61','78'])).

thf('80',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) ) ),
    inference(demod,[status(thm)],['60','79'])).

thf('81',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) ) )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( zip_tseitin_3 @ sk_C @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','80'])).

thf('82',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_3 @ sk_C @ sk_B_1 )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X67: $i,X68: $i] :
      ( ( X67 = k1_xboole_0 )
      | ~ ( zip_tseitin_3 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('84',plain,
    ( ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('85',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('86',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf(t5_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_relat_1 @ C ) )
     => ( ( ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
          & ( ( k1_relat_1 @ C )
            = A ) )
       => ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
          & ( v1_funct_2 @ C @ A @ B )
          & ( v1_funct_1 @ C ) ) ) ) )).

thf(zf_stmt_6,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_0 @ D @ C @ B @ A ) ) )).

thf('89',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( zip_tseitin_0 @ X50 @ X51 @ X52 @ X53 )
      | ( r2_hidden @ X50 @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('90',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X20 @ X19 ) @ ( k2_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X1 @ X3 @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( zip_tseitin_0 @ X50 @ X51 @ X52 @ X53 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X51 @ X50 ) @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ X4 @ X3 @ ( k1_relat_1 @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X0 @ ( k2_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['93'])).

thf(zf_stmt_7,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_0 @ D @ C @ B @ A ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf('95',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( ( k1_relat_1 @ X58 )
       != X57 )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X58 @ X59 @ X57 ) @ X58 @ X59 @ X57 )
      | ( zip_tseitin_1 @ X58 @ X59 @ X57 )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('96',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( v1_relat_1 @ X58 )
      | ~ ( v1_funct_1 @ X58 )
      | ( zip_tseitin_1 @ X58 @ X59 @ ( k1_relat_1 @ X58 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X58 @ X59 @ ( k1_relat_1 @ X58 ) ) @ X58 @ X59 @ ( k1_relat_1 @ X58 ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X55 ) ) )
      | ~ ( zip_tseitin_1 @ X54 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ sk_E ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['88','102'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('104',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('105',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['104'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('106',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('107',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('108',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['54','55'])).

thf('113',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference(demod,[status(thm)],['103','105','110','111','112'])).

thf('114',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('115',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['106','109'])).

thf('119',plain,(
    sk_E = k1_xboole_0 ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['106','109'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('121',plain,(
    ! [X18: $i] :
      ( ( v1_funct_1 @ X18 )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('122',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('123',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( X23
       != ( k1_funct_1 @ X22 @ X21 ) )
      | ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('124',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( r2_hidden @ ( k4_tarski @ X21 @ ( k1_funct_1 @ X22 @ X21 ) ) @ X22 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','131'])).

thf('133',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('134',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('135',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('137',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['132','137'])).

thf('139',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['106','109'])).

thf('140',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['20','119','138','139'])).

thf('141',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('142',plain,
    ( ( k2_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('144',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('146',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['106','109'])).

thf('148',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('151',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_xboole_0 @ sk_D_1 ),
    inference(demod,[status(thm)],['144','146','147','148','151'])).

thf('153',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['7','152'])).

thf('154',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('155',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['155','156'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fcwNCK3kzq
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:19:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.74  % Solved by: fo/fo7.sh
% 0.54/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.74  % done 438 iterations in 0.275s
% 0.54/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.74  % SZS output start Refutation
% 0.54/0.74  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.54/0.74  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.54/0.74  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.54/0.74  thf(sk_B_type, type, sk_B: $i > $i).
% 0.54/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.74  thf(sk_E_type, type, sk_E: $i).
% 0.54/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.74  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.54/0.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.74  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.54/0.74  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.54/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.54/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.74  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.54/0.74  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.54/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.74  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.54/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.74  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.54/0.74  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.54/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.74  thf(sk_F_type, type, sk_F: $i).
% 0.54/0.74  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.54/0.74  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.54/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.74  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.54/0.74  thf(t186_funct_2, conjecture,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.54/0.74       ( ![D:$i]:
% 0.54/0.74         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.54/0.74             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.54/0.74           ( ![E:$i]:
% 0.54/0.74             ( ( ( v1_funct_1 @ E ) & 
% 0.54/0.74                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.54/0.74               ( ![F:$i]:
% 0.54/0.74                 ( ( m1_subset_1 @ F @ B ) =>
% 0.54/0.74                   ( ( r1_tarski @
% 0.54/0.74                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.54/0.74                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.54/0.74                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.54/0.74                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.54/0.74                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.54/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.74    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.74        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.54/0.74          ( ![D:$i]:
% 0.54/0.74            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.54/0.74                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.54/0.74              ( ![E:$i]:
% 0.54/0.74                ( ( ( v1_funct_1 @ E ) & 
% 0.54/0.74                    ( m1_subset_1 @
% 0.54/0.74                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.54/0.74                  ( ![F:$i]:
% 0.54/0.74                    ( ( m1_subset_1 @ F @ B ) =>
% 0.54/0.74                      ( ( r1_tarski @
% 0.54/0.74                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.54/0.74                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.54/0.74                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.54/0.74                          ( ( k1_funct_1 @
% 0.54/0.74                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.54/0.74                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.54/0.74    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 0.54/0.74  thf('0', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(cc6_funct_2, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.54/0.74       ( ![C:$i]:
% 0.54/0.74         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.54/0.74             ( ( v1_funct_1 @ C ) & ( ~( v1_xboole_0 @ C ) ) & 
% 0.54/0.74               ( v1_funct_2 @ C @ A @ B ) ) ) ) ) ))).
% 0.54/0.74  thf('1', plain,
% 0.54/0.74      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.54/0.74         ((v1_xboole_0 @ X38)
% 0.54/0.74          | (v1_xboole_0 @ X39)
% 0.54/0.74          | ~ (v1_funct_1 @ X40)
% 0.54/0.74          | ~ (v1_funct_2 @ X40 @ X38 @ X39)
% 0.54/0.74          | ~ (v1_xboole_0 @ X40)
% 0.54/0.74          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.54/0.74      inference('cnf', [status(esa)], [cc6_funct_2])).
% 0.54/0.74  thf('2', plain,
% 0.54/0.74      ((~ (v1_xboole_0 @ sk_D_1)
% 0.54/0.74        | ~ (v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C)
% 0.54/0.74        | ~ (v1_funct_1 @ sk_D_1)
% 0.54/0.74        | (v1_xboole_0 @ sk_C)
% 0.54/0.74        | (v1_xboole_0 @ sk_B_1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['0', '1'])).
% 0.54/0.74  thf('3', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('4', plain, ((v1_funct_1 @ sk_D_1)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('5', plain,
% 0.54/0.74      ((~ (v1_xboole_0 @ sk_D_1)
% 0.54/0.74        | (v1_xboole_0 @ sk_C)
% 0.54/0.74        | (v1_xboole_0 @ sk_B_1))),
% 0.54/0.74      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.54/0.74  thf('6', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('7', plain, (((v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ sk_D_1))),
% 0.54/0.74      inference('clc', [status(thm)], ['5', '6'])).
% 0.54/0.74  thf('8', plain,
% 0.54/0.74      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.54/0.74        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(t3_subset, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.54/0.74  thf('9', plain,
% 0.54/0.74      (![X15 : $i, X17 : $i]:
% 0.54/0.74         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.54/0.74      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.74  thf('10', plain,
% 0.54/0.74      ((m1_subset_1 @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.54/0.74        (k1_zfmisc_1 @ (k1_relset_1 @ sk_C @ sk_A @ sk_E)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['8', '9'])).
% 0.54/0.74  thf(cc1_subset_1, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( v1_xboole_0 @ A ) =>
% 0.54/0.74       ( ![B:$i]:
% 0.54/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.54/0.74  thf('11', plain,
% 0.54/0.74      (![X11 : $i, X12 : $i]:
% 0.54/0.74         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.54/0.74          | (v1_xboole_0 @ X11)
% 0.54/0.74          | ~ (v1_xboole_0 @ X12))),
% 0.54/0.74      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.54/0.74  thf('12', plain,
% 0.54/0.74      ((~ (v1_xboole_0 @ (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 0.54/0.74        | (v1_xboole_0 @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['10', '11'])).
% 0.54/0.74  thf('13', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(redefinition_k1_relset_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.54/0.74  thf('14', plain,
% 0.54/0.74      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.54/0.74         (((k1_relset_1 @ X33 @ X34 @ X32) = (k1_relat_1 @ X32))
% 0.54/0.74          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.54/0.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.54/0.74  thf('15', plain,
% 0.54/0.74      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.54/0.74      inference('sup-', [status(thm)], ['13', '14'])).
% 0.54/0.74  thf('16', plain,
% 0.54/0.74      ((~ (v1_xboole_0 @ (k1_relat_1 @ sk_E))
% 0.54/0.74        | (v1_xboole_0 @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.54/0.74      inference('demod', [status(thm)], ['12', '15'])).
% 0.54/0.74  thf('17', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(redefinition_k2_relset_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.54/0.74  thf('18', plain,
% 0.54/0.74      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.54/0.74         (((k2_relset_1 @ X36 @ X37 @ X35) = (k2_relat_1 @ X35))
% 0.54/0.74          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.54/0.74      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.54/0.74  thf('19', plain,
% 0.54/0.74      (((k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['17', '18'])).
% 0.54/0.74  thf('20', plain,
% 0.54/0.74      ((~ (v1_xboole_0 @ (k1_relat_1 @ sk_E))
% 0.54/0.74        | (v1_xboole_0 @ (k2_relat_1 @ sk_D_1)))),
% 0.54/0.74      inference('demod', [status(thm)], ['16', '19'])).
% 0.54/0.74  thf('21', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(cc2_relset_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.54/0.74  thf('22', plain,
% 0.54/0.74      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.54/0.74         ((v5_relat_1 @ X29 @ X31)
% 0.54/0.74          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.54/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.74  thf('23', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 0.54/0.74      inference('sup-', [status(thm)], ['21', '22'])).
% 0.54/0.74  thf('24', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(t2_subset, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ A @ B ) =>
% 0.54/0.74       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.54/0.74  thf('25', plain,
% 0.54/0.74      (![X13 : $i, X14 : $i]:
% 0.54/0.74         ((r2_hidden @ X13 @ X14)
% 0.54/0.74          | (v1_xboole_0 @ X14)
% 0.54/0.74          | ~ (m1_subset_1 @ X13 @ X14))),
% 0.54/0.74      inference('cnf', [status(esa)], [t2_subset])).
% 0.54/0.74  thf('26', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['24', '25'])).
% 0.54/0.74  thf('27', plain,
% 0.54/0.74      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.54/0.74        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('28', plain,
% 0.54/0.74      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.54/0.74      inference('sup-', [status(thm)], ['13', '14'])).
% 0.54/0.74  thf('29', plain,
% 0.54/0.74      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.54/0.74        (k1_relat_1 @ sk_E))),
% 0.54/0.74      inference('demod', [status(thm)], ['27', '28'])).
% 0.54/0.74  thf('30', plain,
% 0.54/0.74      (((k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['17', '18'])).
% 0.54/0.74  thf('31', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ (k1_relat_1 @ sk_E))),
% 0.54/0.74      inference('demod', [status(thm)], ['29', '30'])).
% 0.54/0.74  thf('32', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(t8_funct_2, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.74     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.54/0.74         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.54/0.74       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.54/0.74         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.54/0.74             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 0.54/0.74           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.54/0.74  thf(zf_stmt_1, type, zip_tseitin_3 : $i > $i > $o).
% 0.54/0.74  thf(zf_stmt_2, axiom,
% 0.54/0.74    (![B:$i,A:$i]:
% 0.54/0.74     ( ( zip_tseitin_3 @ B @ A ) =>
% 0.54/0.74       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 0.54/0.74  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.54/0.74  thf(zf_stmt_4, axiom,
% 0.54/0.74    (![D:$i,C:$i,A:$i]:
% 0.54/0.74     ( ( zip_tseitin_2 @ D @ C @ A ) =>
% 0.54/0.74       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.54/0.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.54/0.74  thf(zf_stmt_5, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.74     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.54/0.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.74       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.54/0.74         ( ( zip_tseitin_3 @ B @ A ) | ( zip_tseitin_2 @ D @ C @ A ) ) ) ))).
% 0.54/0.74  thf('33', plain,
% 0.54/0.74      (![X69 : $i, X70 : $i, X71 : $i, X72 : $i]:
% 0.54/0.74         ((zip_tseitin_3 @ X69 @ X70)
% 0.54/0.74          | ~ (v1_funct_1 @ X71)
% 0.54/0.74          | ~ (v1_funct_2 @ X71 @ X70 @ X69)
% 0.54/0.74          | ~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X70 @ X69)))
% 0.54/0.74          | (zip_tseitin_2 @ X71 @ X72 @ X70)
% 0.54/0.74          | ~ (r1_tarski @ (k2_relset_1 @ X70 @ X69 @ X71) @ X72))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.54/0.74  thf('34', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) @ X0)
% 0.54/0.74          | (zip_tseitin_2 @ sk_D_1 @ X0 @ sk_B_1)
% 0.54/0.74          | ~ (v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C)
% 0.54/0.74          | ~ (v1_funct_1 @ sk_D_1)
% 0.54/0.74          | (zip_tseitin_3 @ sk_C @ sk_B_1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['32', '33'])).
% 0.54/0.74  thf('35', plain,
% 0.54/0.74      (((k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['17', '18'])).
% 0.54/0.74  thf('36', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('37', plain, ((v1_funct_1 @ sk_D_1)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('38', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0)
% 0.54/0.74          | (zip_tseitin_2 @ sk_D_1 @ X0 @ sk_B_1)
% 0.54/0.74          | (zip_tseitin_3 @ sk_C @ sk_B_1))),
% 0.54/0.74      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.54/0.74  thf('39', plain,
% 0.54/0.74      (((zip_tseitin_3 @ sk_C @ sk_B_1)
% 0.54/0.74        | (zip_tseitin_2 @ sk_D_1 @ (k1_relat_1 @ sk_E) @ sk_B_1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['31', '38'])).
% 0.54/0.74  thf('40', plain,
% 0.54/0.74      (![X64 : $i, X65 : $i, X66 : $i]:
% 0.54/0.74         ((v1_funct_2 @ X64 @ X66 @ X65) | ~ (zip_tseitin_2 @ X64 @ X65 @ X66))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.54/0.74  thf('41', plain,
% 0.54/0.74      (((zip_tseitin_3 @ sk_C @ sk_B_1)
% 0.54/0.74        | (v1_funct_2 @ sk_D_1 @ sk_B_1 @ (k1_relat_1 @ sk_E)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['39', '40'])).
% 0.54/0.74  thf('42', plain,
% 0.54/0.74      (((zip_tseitin_3 @ sk_C @ sk_B_1)
% 0.54/0.74        | (zip_tseitin_2 @ sk_D_1 @ (k1_relat_1 @ sk_E) @ sk_B_1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['31', '38'])).
% 0.54/0.74  thf('43', plain,
% 0.54/0.74      (![X64 : $i, X65 : $i, X66 : $i]:
% 0.54/0.74         ((m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X65)))
% 0.54/0.74          | ~ (zip_tseitin_2 @ X64 @ X65 @ X66))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.54/0.74  thf('44', plain,
% 0.54/0.74      (((zip_tseitin_3 @ sk_C @ sk_B_1)
% 0.54/0.74        | (m1_subset_1 @ sk_D_1 @ 
% 0.54/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ (k1_relat_1 @ sk_E)))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['42', '43'])).
% 0.54/0.74  thf(t7_funct_2, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.74     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.54/0.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.74       ( ( r2_hidden @ C @ A ) =>
% 0.54/0.74         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.54/0.74           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.54/0.74  thf('45', plain,
% 0.54/0.74      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 0.54/0.74         (~ (r2_hidden @ X60 @ X61)
% 0.54/0.74          | ((X62) = (k1_xboole_0))
% 0.54/0.74          | ~ (v1_funct_1 @ X63)
% 0.54/0.74          | ~ (v1_funct_2 @ X63 @ X61 @ X62)
% 0.54/0.74          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X62)))
% 0.54/0.74          | (r2_hidden @ (k1_funct_1 @ X63 @ X60) @ X62))),
% 0.54/0.74      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.54/0.74  thf('46', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((zip_tseitin_3 @ sk_C @ sk_B_1)
% 0.54/0.74          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_relat_1 @ sk_E))
% 0.54/0.74          | ~ (v1_funct_2 @ sk_D_1 @ sk_B_1 @ (k1_relat_1 @ sk_E))
% 0.54/0.74          | ~ (v1_funct_1 @ sk_D_1)
% 0.54/0.74          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.54/0.74          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['44', '45'])).
% 0.54/0.74  thf('47', plain, ((v1_funct_1 @ sk_D_1)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('48', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((zip_tseitin_3 @ sk_C @ sk_B_1)
% 0.54/0.74          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_relat_1 @ sk_E))
% 0.54/0.74          | ~ (v1_funct_2 @ sk_D_1 @ sk_B_1 @ (k1_relat_1 @ sk_E))
% 0.54/0.74          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.54/0.74          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.54/0.74      inference('demod', [status(thm)], ['46', '47'])).
% 0.54/0.74  thf('49', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((zip_tseitin_3 @ sk_C @ sk_B_1)
% 0.54/0.74          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.54/0.74          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.54/0.74          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_relat_1 @ sk_E))
% 0.54/0.74          | (zip_tseitin_3 @ sk_C @ sk_B_1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['41', '48'])).
% 0.54/0.74  thf('50', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_relat_1 @ sk_E))
% 0.54/0.74          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.54/0.74          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.54/0.74          | (zip_tseitin_3 @ sk_C @ sk_B_1))),
% 0.54/0.74      inference('simplify', [status(thm)], ['49'])).
% 0.54/0.74  thf('51', plain,
% 0.54/0.74      (((v1_xboole_0 @ sk_B_1)
% 0.54/0.74        | (zip_tseitin_3 @ sk_C @ sk_B_1)
% 0.54/0.74        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.54/0.74        | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['26', '50'])).
% 0.54/0.74  thf(d8_partfun1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.74       ( ![C:$i]:
% 0.54/0.74         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.54/0.74           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.54/0.74  thf('52', plain,
% 0.54/0.74      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.54/0.74         (~ (r2_hidden @ X41 @ (k1_relat_1 @ X42))
% 0.54/0.74          | ((k7_partfun1 @ X43 @ X42 @ X41) = (k1_funct_1 @ X42 @ X41))
% 0.54/0.74          | ~ (v1_funct_1 @ X42)
% 0.54/0.74          | ~ (v5_relat_1 @ X42 @ X43)
% 0.54/0.74          | ~ (v1_relat_1 @ X42))),
% 0.54/0.74      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.54/0.74  thf('53', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.54/0.74          | (zip_tseitin_3 @ sk_C @ sk_B_1)
% 0.54/0.74          | (v1_xboole_0 @ sk_B_1)
% 0.54/0.74          | ~ (v1_relat_1 @ sk_E)
% 0.54/0.74          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.54/0.74          | ~ (v1_funct_1 @ sk_E)
% 0.54/0.74          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F))
% 0.54/0.74              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['51', '52'])).
% 0.54/0.74  thf('54', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(cc1_relset_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74       ( v1_relat_1 @ C ) ))).
% 0.54/0.74  thf('55', plain,
% 0.54/0.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.54/0.74         ((v1_relat_1 @ X26)
% 0.54/0.74          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.54/0.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.54/0.74  thf('56', plain, ((v1_relat_1 @ sk_E)),
% 0.54/0.74      inference('sup-', [status(thm)], ['54', '55'])).
% 0.54/0.74  thf('57', plain, ((v1_funct_1 @ sk_E)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('58', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.54/0.74          | (zip_tseitin_3 @ sk_C @ sk_B_1)
% 0.54/0.74          | (v1_xboole_0 @ sk_B_1)
% 0.54/0.74          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.54/0.74          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F))
% 0.54/0.74              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F))))),
% 0.54/0.74      inference('demod', [status(thm)], ['53', '56', '57'])).
% 0.54/0.74  thf('59', plain,
% 0.54/0.74      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F))
% 0.54/0.74          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F)))
% 0.54/0.74        | (v1_xboole_0 @ sk_B_1)
% 0.54/0.74        | (zip_tseitin_3 @ sk_C @ sk_B_1)
% 0.54/0.74        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['23', '58'])).
% 0.54/0.74  thf('60', plain,
% 0.54/0.74      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D_1 @ sk_E) @ 
% 0.54/0.74         sk_F) != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('61', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('62', plain,
% 0.54/0.74      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.54/0.74      inference('sup-', [status(thm)], ['13', '14'])).
% 0.54/0.74  thf('63', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(t185_funct_2, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.54/0.74       ( ![D:$i]:
% 0.54/0.74         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.54/0.74             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.54/0.74           ( ![E:$i]:
% 0.54/0.74             ( ( ( v1_funct_1 @ E ) & 
% 0.54/0.74                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.54/0.74               ( ![F:$i]:
% 0.54/0.74                 ( ( m1_subset_1 @ F @ B ) =>
% 0.54/0.74                   ( ( r1_tarski @
% 0.54/0.74                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.54/0.74                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.54/0.74                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.54/0.74                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.54/0.74                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.54/0.74  thf('64', plain,
% 0.54/0.74      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.54/0.74         (~ (v1_funct_1 @ X44)
% 0.54/0.74          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 0.54/0.74          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.54/0.74          | ~ (m1_subset_1 @ X47 @ X45)
% 0.54/0.74          | ((k1_funct_1 @ (k8_funct_2 @ X45 @ X46 @ X49 @ X44 @ X48) @ X47)
% 0.54/0.74              = (k1_funct_1 @ X48 @ (k1_funct_1 @ X44 @ X47)))
% 0.54/0.74          | ((X45) = (k1_xboole_0))
% 0.54/0.74          | ~ (r1_tarski @ (k2_relset_1 @ X45 @ X46 @ X44) @ 
% 0.54/0.74               (k1_relset_1 @ X46 @ X49 @ X48))
% 0.54/0.74          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X49)))
% 0.54/0.74          | ~ (v1_funct_1 @ X48)
% 0.54/0.74          | (v1_xboole_0 @ X46))),
% 0.54/0.74      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.54/0.74  thf('65', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.74         ((v1_xboole_0 @ sk_C)
% 0.54/0.74          | ~ (v1_funct_1 @ X0)
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.54/0.74          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.54/0.74               (k1_relset_1 @ sk_C @ X1 @ X0))
% 0.54/0.74          | ((sk_B_1) = (k1_xboole_0))
% 0.54/0.74          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ X1 @ sk_D_1 @ X0) @ X2)
% 0.54/0.74              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_1 @ X2)))
% 0.54/0.74          | ~ (m1_subset_1 @ X2 @ sk_B_1)
% 0.54/0.74          | ~ (v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C)
% 0.54/0.74          | ~ (v1_funct_1 @ sk_D_1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['63', '64'])).
% 0.54/0.74  thf('66', plain,
% 0.54/0.74      (((k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['17', '18'])).
% 0.54/0.74  thf('67', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('68', plain, ((v1_funct_1 @ sk_D_1)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('69', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.74         ((v1_xboole_0 @ sk_C)
% 0.54/0.74          | ~ (v1_funct_1 @ X0)
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.54/0.74          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ 
% 0.54/0.74               (k1_relset_1 @ sk_C @ X1 @ X0))
% 0.54/0.74          | ((sk_B_1) = (k1_xboole_0))
% 0.54/0.74          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ X1 @ sk_D_1 @ X0) @ X2)
% 0.54/0.74              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_1 @ X2)))
% 0.54/0.74          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 0.54/0.74      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.54/0.74  thf('70', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('71', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.74         ((v1_xboole_0 @ sk_C)
% 0.54/0.74          | ~ (v1_funct_1 @ X0)
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.54/0.74          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ 
% 0.54/0.74               (k1_relset_1 @ sk_C @ X1 @ X0))
% 0.54/0.74          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ X1 @ sk_D_1 @ X0) @ X2)
% 0.54/0.74              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_1 @ X2)))
% 0.54/0.74          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 0.54/0.74      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 0.54/0.74  thf('72', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ (k1_relat_1 @ sk_E))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.54/0.74          | ((k1_funct_1 @ 
% 0.54/0.74              (k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D_1 @ sk_E) @ X0)
% 0.54/0.74              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_1 @ X0)))
% 0.54/0.74          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))
% 0.54/0.74          | ~ (v1_funct_1 @ sk_E)
% 0.54/0.74          | (v1_xboole_0 @ sk_C))),
% 0.54/0.74      inference('sup-', [status(thm)], ['62', '71'])).
% 0.54/0.74  thf('73', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ (k1_relat_1 @ sk_E))),
% 0.54/0.74      inference('demod', [status(thm)], ['29', '30'])).
% 0.54/0.74  thf('74', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('75', plain, ((v1_funct_1 @ sk_E)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('76', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.54/0.74          | ((k1_funct_1 @ 
% 0.54/0.74              (k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D_1 @ sk_E) @ X0)
% 0.54/0.74              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_1 @ X0)))
% 0.54/0.74          | (v1_xboole_0 @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.54/0.74  thf('77', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('78', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D_1 @ sk_E) @ 
% 0.54/0.74            X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_1 @ X0)))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ sk_B_1))),
% 0.54/0.74      inference('clc', [status(thm)], ['76', '77'])).
% 0.54/0.74  thf('79', plain,
% 0.54/0.74      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D_1 @ sk_E) @ 
% 0.54/0.74         sk_F) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['61', '78'])).
% 0.54/0.74  thf('80', plain,
% 0.54/0.74      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F))
% 0.54/0.74         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F)))),
% 0.54/0.74      inference('demod', [status(thm)], ['60', '79'])).
% 0.54/0.74  thf('81', plain,
% 0.54/0.74      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F))
% 0.54/0.74          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F)))
% 0.54/0.74        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.54/0.74        | (zip_tseitin_3 @ sk_C @ sk_B_1)
% 0.54/0.74        | (v1_xboole_0 @ sk_B_1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['59', '80'])).
% 0.54/0.74  thf('82', plain,
% 0.54/0.74      (((v1_xboole_0 @ sk_B_1)
% 0.54/0.74        | (zip_tseitin_3 @ sk_C @ sk_B_1)
% 0.54/0.74        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.54/0.74      inference('simplify', [status(thm)], ['81'])).
% 0.54/0.74  thf('83', plain,
% 0.54/0.74      (![X67 : $i, X68 : $i]:
% 0.54/0.74         (((X67) = (k1_xboole_0)) | ~ (zip_tseitin_3 @ X67 @ X68))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.54/0.74  thf('84', plain,
% 0.54/0.74      ((((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.54/0.74        | (v1_xboole_0 @ sk_B_1)
% 0.54/0.74        | ((sk_C) = (k1_xboole_0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['82', '83'])).
% 0.54/0.74  thf(l13_xboole_0, axiom,
% 0.54/0.74    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.54/0.74  thf('85', plain,
% 0.54/0.74      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.54/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.54/0.74  thf('86', plain,
% 0.54/0.74      ((((sk_C) = (k1_xboole_0))
% 0.54/0.74        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.54/0.74        | ((sk_B_1) = (k1_xboole_0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['84', '85'])).
% 0.54/0.74  thf('87', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('88', plain,
% 0.54/0.74      ((((sk_C) = (k1_xboole_0)) | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.54/0.74      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 0.54/0.74  thf(t5_funct_2, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.54/0.74       ( ( ( ![D:$i]:
% 0.54/0.74             ( ( r2_hidden @ D @ A ) =>
% 0.54/0.74               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 0.54/0.74           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.54/0.74         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.54/0.74           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 0.54/0.74  thf(zf_stmt_6, axiom,
% 0.54/0.74    (![D:$i,C:$i,B:$i,A:$i]:
% 0.54/0.74     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 0.54/0.74       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 0.54/0.74  thf('89', plain,
% 0.54/0.74      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.54/0.74         ((zip_tseitin_0 @ X50 @ X51 @ X52 @ X53) | (r2_hidden @ X50 @ X53))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.54/0.74  thf(t12_funct_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.74       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.54/0.74         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.54/0.74  thf('90', plain,
% 0.54/0.74      (![X19 : $i, X20 : $i]:
% 0.54/0.74         (~ (r2_hidden @ X19 @ (k1_relat_1 @ X20))
% 0.54/0.74          | (r2_hidden @ (k1_funct_1 @ X20 @ X19) @ (k2_relat_1 @ X20))
% 0.54/0.74          | ~ (v1_funct_1 @ X20)
% 0.54/0.74          | ~ (v1_relat_1 @ X20))),
% 0.54/0.74      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.54/0.74  thf('91', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.74         ((zip_tseitin_0 @ X1 @ X3 @ X2 @ (k1_relat_1 @ X0))
% 0.54/0.74          | ~ (v1_relat_1 @ X0)
% 0.54/0.74          | ~ (v1_funct_1 @ X0)
% 0.54/0.74          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ (k2_relat_1 @ X0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['89', '90'])).
% 0.54/0.74  thf('92', plain,
% 0.54/0.74      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.54/0.74         ((zip_tseitin_0 @ X50 @ X51 @ X52 @ X53)
% 0.54/0.74          | ~ (r2_hidden @ (k1_funct_1 @ X51 @ X50) @ X52))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.54/0.74  thf('93', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.54/0.74         (~ (v1_funct_1 @ X0)
% 0.54/0.74          | ~ (v1_relat_1 @ X0)
% 0.54/0.74          | (zip_tseitin_0 @ X1 @ X4 @ X3 @ (k1_relat_1 @ X0))
% 0.54/0.74          | (zip_tseitin_0 @ X1 @ X0 @ (k2_relat_1 @ X0) @ X2))),
% 0.54/0.74      inference('sup-', [status(thm)], ['91', '92'])).
% 0.54/0.74  thf('94', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         ((zip_tseitin_0 @ X1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.54/0.74          | ~ (v1_relat_1 @ X0)
% 0.54/0.74          | ~ (v1_funct_1 @ X0))),
% 0.54/0.74      inference('eq_fact', [status(thm)], ['93'])).
% 0.54/0.74  thf(zf_stmt_7, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.54/0.74  thf(zf_stmt_8, axiom,
% 0.54/0.74    (![C:$i,B:$i,A:$i]:
% 0.54/0.74     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.54/0.74       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.54/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.54/0.74  thf(zf_stmt_9, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.54/0.74  thf(zf_stmt_10, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.54/0.74       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.54/0.74           ( ![D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) =>
% 0.54/0.74         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.54/0.74  thf('95', plain,
% 0.54/0.74      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.54/0.74         (((k1_relat_1 @ X58) != (X57))
% 0.54/0.74          | ~ (zip_tseitin_0 @ (sk_D @ X58 @ X59 @ X57) @ X58 @ X59 @ X57)
% 0.54/0.74          | (zip_tseitin_1 @ X58 @ X59 @ X57)
% 0.54/0.74          | ~ (v1_funct_1 @ X58)
% 0.54/0.74          | ~ (v1_relat_1 @ X58))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_10])).
% 0.54/0.74  thf('96', plain,
% 0.54/0.74      (![X58 : $i, X59 : $i]:
% 0.54/0.74         (~ (v1_relat_1 @ X58)
% 0.54/0.74          | ~ (v1_funct_1 @ X58)
% 0.54/0.74          | (zip_tseitin_1 @ X58 @ X59 @ (k1_relat_1 @ X58))
% 0.54/0.74          | ~ (zip_tseitin_0 @ (sk_D @ X58 @ X59 @ (k1_relat_1 @ X58)) @ X58 @ 
% 0.54/0.74               X59 @ (k1_relat_1 @ X58)))),
% 0.54/0.74      inference('simplify', [status(thm)], ['95'])).
% 0.54/0.74  thf('97', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v1_funct_1 @ X0)
% 0.54/0.74          | ~ (v1_relat_1 @ X0)
% 0.54/0.74          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.54/0.74          | ~ (v1_funct_1 @ X0)
% 0.54/0.74          | ~ (v1_relat_1 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['94', '96'])).
% 0.54/0.74  thf('98', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.54/0.74          | ~ (v1_relat_1 @ X0)
% 0.54/0.74          | ~ (v1_funct_1 @ X0))),
% 0.54/0.74      inference('simplify', [status(thm)], ['97'])).
% 0.54/0.74  thf('99', plain,
% 0.54/0.74      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.54/0.74         ((m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X55)))
% 0.54/0.74          | ~ (zip_tseitin_1 @ X54 @ X55 @ X56))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.54/0.74  thf('100', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v1_funct_1 @ X0)
% 0.54/0.74          | ~ (v1_relat_1 @ X0)
% 0.54/0.74          | (m1_subset_1 @ X0 @ 
% 0.54/0.74             (k1_zfmisc_1 @ 
% 0.54/0.74              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['98', '99'])).
% 0.54/0.74  thf('101', plain,
% 0.54/0.74      (![X11 : $i, X12 : $i]:
% 0.54/0.74         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.54/0.74          | (v1_xboole_0 @ X11)
% 0.54/0.74          | ~ (v1_xboole_0 @ X12))),
% 0.54/0.74      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.54/0.74  thf('102', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v1_relat_1 @ X0)
% 0.54/0.74          | ~ (v1_funct_1 @ X0)
% 0.54/0.74          | ~ (v1_xboole_0 @ 
% 0.54/0.74               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.54/0.74          | (v1_xboole_0 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['100', '101'])).
% 0.54/0.74  thf('103', plain,
% 0.54/0.74      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ sk_E)))
% 0.54/0.74        | ((sk_C) = (k1_xboole_0))
% 0.54/0.74        | (v1_xboole_0 @ sk_E)
% 0.54/0.74        | ~ (v1_funct_1 @ sk_E)
% 0.54/0.74        | ~ (v1_relat_1 @ sk_E))),
% 0.54/0.74      inference('sup-', [status(thm)], ['88', '102'])).
% 0.54/0.74  thf(t113_zfmisc_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.54/0.74       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.54/0.74  thf('104', plain,
% 0.54/0.74      (![X9 : $i, X10 : $i]:
% 0.54/0.74         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.54/0.74      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.54/0.74  thf('105', plain,
% 0.54/0.74      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.54/0.74      inference('simplify', [status(thm)], ['104'])).
% 0.54/0.74  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.54/0.74  thf('106', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.54/0.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.74  thf(d1_xboole_0, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.54/0.74  thf('107', plain,
% 0.54/0.74      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.54/0.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.54/0.74  thf(t7_ordinal1, axiom,
% 0.54/0.74    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.74  thf('108', plain,
% 0.54/0.74      (![X24 : $i, X25 : $i]:
% 0.54/0.74         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 0.54/0.74      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.54/0.74  thf('109', plain,
% 0.54/0.74      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['107', '108'])).
% 0.54/0.74  thf('110', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.74      inference('sup-', [status(thm)], ['106', '109'])).
% 0.54/0.74  thf('111', plain, ((v1_funct_1 @ sk_E)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('112', plain, ((v1_relat_1 @ sk_E)),
% 0.54/0.74      inference('sup-', [status(thm)], ['54', '55'])).
% 0.54/0.74  thf('113', plain, ((((sk_C) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E))),
% 0.54/0.74      inference('demod', [status(thm)], ['103', '105', '110', '111', '112'])).
% 0.54/0.74  thf('114', plain,
% 0.54/0.74      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.54/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.54/0.74  thf('115', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_E) = (k1_xboole_0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['113', '114'])).
% 0.54/0.74  thf('116', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('117', plain,
% 0.54/0.74      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_E) = (k1_xboole_0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['115', '116'])).
% 0.54/0.74  thf('118', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.74      inference('sup-', [status(thm)], ['106', '109'])).
% 0.54/0.74  thf('119', plain, (((sk_E) = (k1_xboole_0))),
% 0.54/0.74      inference('demod', [status(thm)], ['117', '118'])).
% 0.54/0.74  thf('120', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.74      inference('sup-', [status(thm)], ['106', '109'])).
% 0.54/0.74  thf(cc1_funct_1, axiom,
% 0.54/0.74    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.54/0.74  thf('121', plain,
% 0.54/0.74      (![X18 : $i]: ((v1_funct_1 @ X18) | ~ (v1_xboole_0 @ X18))),
% 0.54/0.74      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.54/0.74  thf('122', plain,
% 0.54/0.74      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.54/0.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.54/0.74  thf(t8_funct_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.54/0.74       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.54/0.74         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.54/0.74           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.54/0.74  thf('123', plain,
% 0.54/0.74      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.54/0.74         (~ (r2_hidden @ X21 @ (k1_relat_1 @ X22))
% 0.54/0.74          | ((X23) != (k1_funct_1 @ X22 @ X21))
% 0.54/0.74          | (r2_hidden @ (k4_tarski @ X21 @ X23) @ X22)
% 0.54/0.74          | ~ (v1_funct_1 @ X22)
% 0.54/0.74          | ~ (v1_relat_1 @ X22))),
% 0.54/0.74      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.54/0.74  thf('124', plain,
% 0.54/0.74      (![X21 : $i, X22 : $i]:
% 0.54/0.74         (~ (v1_relat_1 @ X22)
% 0.54/0.74          | ~ (v1_funct_1 @ X22)
% 0.54/0.74          | (r2_hidden @ (k4_tarski @ X21 @ (k1_funct_1 @ X22 @ X21)) @ X22)
% 0.54/0.74          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X22)))),
% 0.54/0.74      inference('simplify', [status(thm)], ['123'])).
% 0.54/0.74  thf('125', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.54/0.74          | (r2_hidden @ 
% 0.54/0.74             (k4_tarski @ (sk_B @ (k1_relat_1 @ X0)) @ 
% 0.54/0.74              (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0)))) @ 
% 0.54/0.74             X0)
% 0.54/0.74          | ~ (v1_funct_1 @ X0)
% 0.54/0.74          | ~ (v1_relat_1 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['122', '124'])).
% 0.54/0.74  thf('126', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.54/0.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.54/0.74  thf('127', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v1_relat_1 @ X0)
% 0.54/0.74          | ~ (v1_funct_1 @ X0)
% 0.54/0.74          | (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.54/0.74          | ~ (v1_xboole_0 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['125', '126'])).
% 0.54/0.74  thf('128', plain,
% 0.54/0.74      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.54/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.54/0.74  thf('129', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v1_xboole_0 @ X0)
% 0.54/0.74          | ~ (v1_funct_1 @ X0)
% 0.54/0.74          | ~ (v1_relat_1 @ X0)
% 0.54/0.74          | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['127', '128'])).
% 0.54/0.74  thf('130', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v1_xboole_0 @ X0)
% 0.54/0.74          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.54/0.74          | ~ (v1_relat_1 @ X0)
% 0.54/0.74          | ~ (v1_xboole_0 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['121', '129'])).
% 0.54/0.74  thf('131', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v1_relat_1 @ X0)
% 0.54/0.74          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.54/0.74          | ~ (v1_xboole_0 @ X0))),
% 0.54/0.74      inference('simplify', [status(thm)], ['130'])).
% 0.54/0.74  thf('132', plain,
% 0.54/0.74      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.54/0.74        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['120', '131'])).
% 0.54/0.74  thf('133', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.54/0.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.74  thf('134', plain,
% 0.54/0.74      (![X15 : $i, X17 : $i]:
% 0.54/0.74         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.54/0.74      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.74  thf('135', plain,
% 0.54/0.74      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['133', '134'])).
% 0.54/0.74  thf('136', plain,
% 0.54/0.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.54/0.74         ((v1_relat_1 @ X26)
% 0.54/0.74          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.54/0.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.54/0.74  thf('137', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.54/0.74      inference('sup-', [status(thm)], ['135', '136'])).
% 0.54/0.74  thf('138', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.74      inference('demod', [status(thm)], ['132', '137'])).
% 0.54/0.74  thf('139', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.74      inference('sup-', [status(thm)], ['106', '109'])).
% 0.54/0.74  thf('140', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_D_1))),
% 0.54/0.74      inference('demod', [status(thm)], ['20', '119', '138', '139'])).
% 0.54/0.74  thf('141', plain,
% 0.54/0.74      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.54/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.54/0.74  thf('142', plain, (((k2_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['140', '141'])).
% 0.54/0.74  thf('143', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v1_relat_1 @ X0)
% 0.54/0.74          | ~ (v1_funct_1 @ X0)
% 0.54/0.74          | ~ (v1_xboole_0 @ 
% 0.54/0.74               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.54/0.74          | (v1_xboole_0 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['100', '101'])).
% 0.54/0.74  thf('144', plain,
% 0.54/0.74      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ k1_xboole_0))
% 0.54/0.74        | (v1_xboole_0 @ sk_D_1)
% 0.54/0.74        | ~ (v1_funct_1 @ sk_D_1)
% 0.54/0.74        | ~ (v1_relat_1 @ sk_D_1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['142', '143'])).
% 0.54/0.74  thf('145', plain,
% 0.54/0.74      (![X9 : $i, X10 : $i]:
% 0.54/0.74         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 0.54/0.74      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.54/0.74  thf('146', plain,
% 0.54/0.74      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.74      inference('simplify', [status(thm)], ['145'])).
% 0.54/0.74  thf('147', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.74      inference('sup-', [status(thm)], ['106', '109'])).
% 0.54/0.74  thf('148', plain, ((v1_funct_1 @ sk_D_1)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('149', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('150', plain,
% 0.54/0.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.54/0.74         ((v1_relat_1 @ X26)
% 0.54/0.74          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.54/0.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.54/0.74  thf('151', plain, ((v1_relat_1 @ sk_D_1)),
% 0.54/0.74      inference('sup-', [status(thm)], ['149', '150'])).
% 0.54/0.74  thf('152', plain, ((v1_xboole_0 @ sk_D_1)),
% 0.54/0.74      inference('demod', [status(thm)], ['144', '146', '147', '148', '151'])).
% 0.54/0.74  thf('153', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.54/0.74      inference('demod', [status(thm)], ['7', '152'])).
% 0.54/0.74  thf('154', plain,
% 0.54/0.74      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.54/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.54/0.74  thf('155', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['153', '154'])).
% 0.54/0.74  thf('156', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('157', plain, ($false),
% 0.54/0.74      inference('simplify_reflect-', [status(thm)], ['155', '156'])).
% 0.54/0.74  
% 0.54/0.74  % SZS output end Refutation
% 0.54/0.74  
% 0.54/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2S7Cz7qvHC

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 302 expanded)
%              Number of leaves         :   50 ( 110 expanded)
%              Depth                    :   28
%              Number of atoms          : 1432 (6036 expanded)
%              Number of equality atoms :   76 ( 260 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc6_funct_2])).

thf('2',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v5_relat_1 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('10',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
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
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_1 @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( A != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ A )
     => ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( zip_tseitin_1 @ B @ A )
          | ( zip_tseitin_0 @ D @ C @ A ) ) ) ) )).

thf('20',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( zip_tseitin_1 @ X53 @ X54 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_2 @ X55 @ X54 @ X53 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X53 ) ) )
      | ( zip_tseitin_0 @ X55 @ X56 @ X54 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X54 @ X53 @ X55 ) @ X56 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( zip_tseitin_0 @ sk_D @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( zip_tseitin_0 @ sk_D @ X0 @ sk_B )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ ( k1_relat_1 @ sk_E ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( v1_funct_2 @ X48 @ X50 @ X49 )
      | ~ ( zip_tseitin_0 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('27',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B )
    | ( v1_funct_2 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ ( k1_relat_1 @ sk_E ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('29',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) )
      | ~ ( zip_tseitin_0 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('30',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('31',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X44 @ X45 )
      | ( X46 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X47 @ X44 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C_1 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C_1 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_E ) )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C_1 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['13','36'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('38',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X35 @ ( k1_relat_1 @ X36 ) )
      | ( ( k7_partfun1 @ X37 @ X36 @ X35 )
        = ( k1_funct_1 @ X36 @ X35 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v5_relat_1 @ X36 @ X37 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('41',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('42',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['39','42','43'])).

thf('45',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','44'])).

thf('46',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
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

thf('50',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X41 @ X39 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X39 @ X40 @ X43 @ X38 @ X42 ) @ X41 )
        = ( k1_funct_1 @ X42 @ ( k1_funct_1 @ X38 @ X41 ) ) )
      | ( X39 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X39 @ X40 @ X38 ) @ ( k1_relset_1 @ X40 @ X43 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('59',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['47','63'])).

thf('65',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['46','64'])).

thf('66',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X51: $i,X52: $i] :
      ( ( X51 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('69',plain,
    ( ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('70',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('71',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('75',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('76',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_E ) ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ k1_xboole_0 ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('78',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('79',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('80',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('81',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('82',plain,(
    ! [X13: $i,X14: $i] :
      ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('83',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('85',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('87',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('88',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['77','79','88'])).

thf('90',plain,(
    ! [X51: $i,X52: $i] :
      ( ( X51 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('91',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('93',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['86','87'])).

thf('97',plain,(
    sk_D = k1_xboole_0 ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['86','87'])).

thf('99',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['7','97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('101',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2S7Cz7qvHC
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:24:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 307 iterations in 0.110s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.58  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.21/0.58  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.21/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.21/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.58  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.21/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.58  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(t186_funct_2, conjecture,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.58       ( ![D:$i]:
% 0.21/0.58         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.58             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.58           ( ![E:$i]:
% 0.21/0.58             ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.58                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.21/0.58               ( ![F:$i]:
% 0.21/0.58                 ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.58                   ( ( r1_tarski @
% 0.21/0.58                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.21/0.58                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.21/0.58                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.58                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.21/0.58                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.58        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.58          ( ![D:$i]:
% 0.21/0.58            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.58                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.58              ( ![E:$i]:
% 0.21/0.58                ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.58                    ( m1_subset_1 @
% 0.21/0.58                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.21/0.58                  ( ![F:$i]:
% 0.21/0.58                    ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.58                      ( ( r1_tarski @
% 0.21/0.58                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.21/0.58                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.21/0.58                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.58                          ( ( k1_funct_1 @
% 0.21/0.58                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.21/0.58                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 0.21/0.58  thf('0', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(cc6_funct_2, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.21/0.58       ( ![C:$i]:
% 0.21/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.21/0.58             ( ( v1_funct_1 @ C ) & ( ~( v1_xboole_0 @ C ) ) & 
% 0.21/0.58               ( v1_funct_2 @ C @ A @ B ) ) ) ) ) ))).
% 0.21/0.58  thf('1', plain,
% 0.21/0.58      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ X32)
% 0.21/0.58          | (v1_xboole_0 @ X33)
% 0.21/0.58          | ~ (v1_funct_1 @ X34)
% 0.21/0.58          | ~ (v1_funct_2 @ X34 @ X32 @ X33)
% 0.21/0.58          | ~ (v1_xboole_0 @ X34)
% 0.21/0.58          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc6_funct_2])).
% 0.21/0.58  thf('2', plain,
% 0.21/0.58      ((~ (v1_xboole_0 @ sk_D)
% 0.21/0.58        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C_1)
% 0.21/0.58        | ~ (v1_funct_1 @ sk_D)
% 0.21/0.58        | (v1_xboole_0 @ sk_C_1)
% 0.21/0.58        | (v1_xboole_0 @ sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.58  thf('3', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C_1)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('5', plain,
% 0.21/0.58      ((~ (v1_xboole_0 @ sk_D) | (v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.21/0.58  thf('6', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('7', plain, (((v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_D))),
% 0.21/0.58      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(cc2_relset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.58  thf('9', plain,
% 0.21/0.58      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.58         ((v5_relat_1 @ X26 @ X28)
% 0.21/0.58          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.58  thf('10', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 0.21/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.58  thf('11', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t2_subset, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.58       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      (![X17 : $i, X18 : $i]:
% 0.21/0.58         ((r2_hidden @ X17 @ X18)
% 0.21/0.58          | (v1_xboole_0 @ X18)
% 0.21/0.58          | ~ (m1_subset_1 @ X17 @ X18))),
% 0.21/0.58      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.58  thf('13', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.21/0.58        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('15', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.58         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.21/0.58          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.21/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.21/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.21/0.58      inference('demod', [status(thm)], ['14', '17'])).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t8_funct_2, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.58     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.58         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.21/0.58       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.21/0.58         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.21/0.58             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 0.21/0.58           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.21/0.58  thf(zf_stmt_2, axiom,
% 0.21/0.58    (![B:$i,A:$i]:
% 0.21/0.58     ( ( zip_tseitin_1 @ B @ A ) =>
% 0.21/0.58       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.21/0.58  thf(zf_stmt_4, axiom,
% 0.21/0.58    (![D:$i,C:$i,A:$i]:
% 0.21/0.58     ( ( zip_tseitin_0 @ D @ C @ A ) =>
% 0.21/0.58       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.21/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_5, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.58     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.58       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.21/0.58         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ A ) ) ) ))).
% 0.21/0.58  thf('20', plain,
% 0.21/0.58      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 0.21/0.58         ((zip_tseitin_1 @ X53 @ X54)
% 0.21/0.58          | ~ (v1_funct_1 @ X55)
% 0.21/0.58          | ~ (v1_funct_2 @ X55 @ X54 @ X53)
% 0.21/0.58          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X53)))
% 0.21/0.58          | (zip_tseitin_0 @ X55 @ X56 @ X54)
% 0.21/0.58          | ~ (r1_tarski @ (k2_relset_1 @ X54 @ X53 @ X55) @ X56))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.58  thf('21', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ X0)
% 0.21/0.58          | (zip_tseitin_0 @ sk_D @ X0 @ sk_B)
% 0.21/0.58          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C_1)
% 0.21/0.58          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.58          | (zip_tseitin_1 @ sk_C_1 @ sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.58  thf('22', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C_1)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('24', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ X0)
% 0.21/0.58          | (zip_tseitin_0 @ sk_D @ X0 @ sk_B)
% 0.21/0.58          | (zip_tseitin_1 @ sk_C_1 @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      (((zip_tseitin_1 @ sk_C_1 @ sk_B)
% 0.21/0.58        | (zip_tseitin_0 @ sk_D @ (k1_relat_1 @ sk_E) @ sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['18', '24'])).
% 0.21/0.58  thf('26', plain,
% 0.21/0.58      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.21/0.58         ((v1_funct_2 @ X48 @ X50 @ X49) | ~ (zip_tseitin_0 @ X48 @ X49 @ X50))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.58  thf('27', plain,
% 0.21/0.58      (((zip_tseitin_1 @ sk_C_1 @ sk_B)
% 0.21/0.58        | (v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.58  thf('28', plain,
% 0.21/0.58      (((zip_tseitin_1 @ sk_C_1 @ sk_B)
% 0.21/0.58        | (zip_tseitin_0 @ sk_D @ (k1_relat_1 @ sk_E) @ sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['18', '24'])).
% 0.21/0.58  thf('29', plain,
% 0.21/0.58      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.21/0.58         ((m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49)))
% 0.21/0.58          | ~ (zip_tseitin_0 @ X48 @ X49 @ X50))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.58  thf('30', plain,
% 0.21/0.58      (((zip_tseitin_1 @ sk_C_1 @ sk_B)
% 0.21/0.58        | (m1_subset_1 @ sk_D @ 
% 0.21/0.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E)))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.58  thf(t7_funct_2, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.58     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.59       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.59           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.21/0.59  thf('31', plain,
% 0.21/0.59      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.21/0.59         (~ (r2_hidden @ X44 @ X45)
% 0.21/0.59          | ((X46) = (k1_xboole_0))
% 0.21/0.59          | ~ (v1_funct_1 @ X47)
% 0.21/0.59          | ~ (v1_funct_2 @ X47 @ X45 @ X46)
% 0.21/0.59          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.21/0.59          | (r2_hidden @ (k1_funct_1 @ X47 @ X44) @ X46))),
% 0.21/0.59      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.21/0.59  thf('32', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         ((zip_tseitin_1 @ sk_C_1 @ sk_B)
% 0.21/0.59          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.21/0.59          | ~ (v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E))
% 0.21/0.59          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.59          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.21/0.59          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.59  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('34', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         ((zip_tseitin_1 @ sk_C_1 @ sk_B)
% 0.21/0.59          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.21/0.59          | ~ (v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E))
% 0.21/0.59          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.21/0.59          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.59      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.59  thf('35', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         ((zip_tseitin_1 @ sk_C_1 @ sk_B)
% 0.21/0.59          | ~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.59          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.21/0.59          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.21/0.59          | (zip_tseitin_1 @ sk_C_1 @ sk_B))),
% 0.21/0.59      inference('sup-', [status(thm)], ['27', '34'])).
% 0.21/0.59  thf('36', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.21/0.59          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.21/0.59          | ~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.59          | (zip_tseitin_1 @ sk_C_1 @ sk_B))),
% 0.21/0.59      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.59  thf('37', plain,
% 0.21/0.59      (((v1_xboole_0 @ sk_B)
% 0.21/0.59        | (zip_tseitin_1 @ sk_C_1 @ sk_B)
% 0.21/0.59        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.21/0.59        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['13', '36'])).
% 0.21/0.59  thf(d8_partfun1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.59       ( ![C:$i]:
% 0.21/0.59         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.59           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.21/0.59  thf('38', plain,
% 0.21/0.59      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.59         (~ (r2_hidden @ X35 @ (k1_relat_1 @ X36))
% 0.21/0.59          | ((k7_partfun1 @ X37 @ X36 @ X35) = (k1_funct_1 @ X36 @ X35))
% 0.21/0.59          | ~ (v1_funct_1 @ X36)
% 0.21/0.59          | ~ (v5_relat_1 @ X36 @ X37)
% 0.21/0.59          | ~ (v1_relat_1 @ X36))),
% 0.21/0.59      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.21/0.59  thf('39', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.21/0.59          | (zip_tseitin_1 @ sk_C_1 @ sk_B)
% 0.21/0.59          | (v1_xboole_0 @ sk_B)
% 0.21/0.59          | ~ (v1_relat_1 @ sk_E)
% 0.21/0.59          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.21/0.59          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.59          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.59              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.21/0.59      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.59  thf('40', plain,
% 0.21/0.59      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(cc1_relset_1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.59       ( v1_relat_1 @ C ) ))).
% 0.21/0.59  thf('41', plain,
% 0.21/0.59      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.59         ((v1_relat_1 @ X23)
% 0.21/0.59          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.21/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.59  thf('42', plain, ((v1_relat_1 @ sk_E)),
% 0.21/0.59      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.59  thf('43', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('44', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.21/0.59          | (zip_tseitin_1 @ sk_C_1 @ sk_B)
% 0.21/0.59          | (v1_xboole_0 @ sk_B)
% 0.21/0.59          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.21/0.59          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.59              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.21/0.59      inference('demod', [status(thm)], ['39', '42', '43'])).
% 0.21/0.59  thf('45', plain,
% 0.21/0.59      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.59          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.21/0.59        | (v1_xboole_0 @ sk_B)
% 0.21/0.59        | (zip_tseitin_1 @ sk_C_1 @ sk_B)
% 0.21/0.59        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['10', '44'])).
% 0.21/0.59  thf('46', plain,
% 0.21/0.59      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.21/0.59         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('47', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('48', plain,
% 0.21/0.59      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.21/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.59  thf('49', plain,
% 0.21/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(t185_funct_2, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.59       ( ![D:$i]:
% 0.21/0.59         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.59             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.59           ( ![E:$i]:
% 0.21/0.59             ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.59                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.21/0.59               ( ![F:$i]:
% 0.21/0.59                 ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.59                   ( ( r1_tarski @
% 0.21/0.59                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.21/0.59                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.21/0.59                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.59                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.21/0.59                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.59  thf('50', plain,
% 0.21/0.59      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.21/0.59         (~ (v1_funct_1 @ X38)
% 0.21/0.59          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 0.21/0.59          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.21/0.59          | ~ (m1_subset_1 @ X41 @ X39)
% 0.21/0.59          | ((k1_funct_1 @ (k8_funct_2 @ X39 @ X40 @ X43 @ X38 @ X42) @ X41)
% 0.21/0.59              = (k1_funct_1 @ X42 @ (k1_funct_1 @ X38 @ X41)))
% 0.21/0.59          | ((X39) = (k1_xboole_0))
% 0.21/0.59          | ~ (r1_tarski @ (k2_relset_1 @ X39 @ X40 @ X38) @ 
% 0.21/0.59               (k1_relset_1 @ X40 @ X43 @ X42))
% 0.21/0.59          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X43)))
% 0.21/0.59          | ~ (v1_funct_1 @ X42)
% 0.21/0.59          | (v1_xboole_0 @ X40))),
% 0.21/0.59      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.21/0.59  thf('51', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         ((v1_xboole_0 @ sk_C_1)
% 0.21/0.59          | ~ (v1_funct_1 @ X0)
% 0.21/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.21/0.59          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.21/0.59               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.21/0.59          | ((sk_B) = (k1_xboole_0))
% 0.21/0.59          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.21/0.59              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.21/0.59          | ~ (m1_subset_1 @ X2 @ sk_B)
% 0.21/0.59          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C_1)
% 0.21/0.59          | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.59      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.59  thf('52', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C_1)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('53', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('54', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         ((v1_xboole_0 @ sk_C_1)
% 0.21/0.59          | ~ (v1_funct_1 @ X0)
% 0.21/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.21/0.59          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.21/0.59               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.21/0.59          | ((sk_B) = (k1_xboole_0))
% 0.21/0.59          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.21/0.59              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.21/0.59          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.21/0.59      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.21/0.59  thf('55', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('56', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         ((v1_xboole_0 @ sk_C_1)
% 0.21/0.59          | ~ (v1_funct_1 @ X0)
% 0.21/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.21/0.59          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.21/0.59               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.21/0.59          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.21/0.59              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.21/0.59          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.21/0.59      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.21/0.59  thf('57', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.21/0.59             (k1_relat_1 @ sk_E))
% 0.21/0.59          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.59          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.21/0.59              X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.21/0.59          | ~ (m1_subset_1 @ sk_E @ 
% 0.21/0.59               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 0.21/0.59          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.59          | (v1_xboole_0 @ sk_C_1))),
% 0.21/0.59      inference('sup-', [status(thm)], ['48', '56'])).
% 0.21/0.59  thf('58', plain,
% 0.21/0.59      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.21/0.59      inference('demod', [status(thm)], ['14', '17'])).
% 0.21/0.59  thf('59', plain,
% 0.21/0.59      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('60', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('61', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.59          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.21/0.59              X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.21/0.59          | (v1_xboole_0 @ sk_C_1))),
% 0.21/0.59      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.21/0.59  thf('62', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('63', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.21/0.59            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.21/0.59          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 0.21/0.59      inference('clc', [status(thm)], ['61', '62'])).
% 0.21/0.59  thf('64', plain,
% 0.21/0.59      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.21/0.59         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['47', '63'])).
% 0.21/0.59  thf('65', plain,
% 0.21/0.59      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.59         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.59      inference('demod', [status(thm)], ['46', '64'])).
% 0.21/0.59  thf('66', plain,
% 0.21/0.59      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.59          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.21/0.59        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.21/0.59        | (zip_tseitin_1 @ sk_C_1 @ sk_B)
% 0.21/0.59        | (v1_xboole_0 @ sk_B))),
% 0.21/0.59      inference('sup-', [status(thm)], ['45', '65'])).
% 0.21/0.59  thf('67', plain,
% 0.21/0.59      (((v1_xboole_0 @ sk_B)
% 0.21/0.59        | (zip_tseitin_1 @ sk_C_1 @ sk_B)
% 0.21/0.59        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.21/0.59      inference('simplify', [status(thm)], ['66'])).
% 0.21/0.59  thf('68', plain,
% 0.21/0.59      (![X51 : $i, X52 : $i]:
% 0.21/0.59         (((X51) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X51 @ X52))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.59  thf('69', plain,
% 0.21/0.59      ((((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.21/0.59        | (v1_xboole_0 @ sk_B)
% 0.21/0.59        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.59  thf(l13_xboole_0, axiom,
% 0.21/0.59    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.59  thf('70', plain,
% 0.21/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.59  thf('71', plain,
% 0.21/0.59      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.59        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.21/0.59        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.59  thf('72', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('73', plain,
% 0.21/0.59      ((((sk_C_1) = (k1_xboole_0)) | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.21/0.59      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 0.21/0.59  thf('74', plain,
% 0.21/0.59      (((zip_tseitin_1 @ sk_C_1 @ sk_B)
% 0.21/0.59        | (m1_subset_1 @ sk_D @ 
% 0.21/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E)))))),
% 0.21/0.59      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.59  thf(cc1_subset_1, axiom,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.59       ( ![B:$i]:
% 0.21/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.21/0.59  thf('75', plain,
% 0.21/0.59      (![X15 : $i, X16 : $i]:
% 0.21/0.59         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.21/0.59          | (v1_xboole_0 @ X15)
% 0.21/0.59          | ~ (v1_xboole_0 @ X16))),
% 0.21/0.59      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.21/0.59  thf('76', plain,
% 0.21/0.59      (((zip_tseitin_1 @ sk_C_1 @ sk_B)
% 0.21/0.59        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E)))
% 0.21/0.59        | (v1_xboole_0 @ sk_D))),
% 0.21/0.59      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.59  thf('77', plain,
% 0.21/0.59      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ k1_xboole_0))
% 0.21/0.59        | ((sk_C_1) = (k1_xboole_0))
% 0.21/0.59        | (v1_xboole_0 @ sk_D)
% 0.21/0.59        | (zip_tseitin_1 @ sk_C_1 @ sk_B))),
% 0.21/0.59      inference('sup-', [status(thm)], ['73', '76'])).
% 0.21/0.59  thf(t113_zfmisc_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.59       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.59  thf('78', plain,
% 0.21/0.59      (![X11 : $i, X12 : $i]:
% 0.21/0.59         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.21/0.59          | ((X12) != (k1_xboole_0)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.59  thf('79', plain,
% 0.21/0.59      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.59      inference('simplify', [status(thm)], ['78'])).
% 0.21/0.59  thf(t3_xboole_0, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.59            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.59  thf('80', plain,
% 0.21/0.59      (![X1 : $i, X2 : $i]:
% 0.21/0.59         ((r1_xboole_0 @ X1 @ X2) | (r2_hidden @ (sk_C @ X2 @ X1) @ X1))),
% 0.21/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.59  thf('81', plain,
% 0.21/0.59      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.59      inference('simplify', [status(thm)], ['78'])).
% 0.21/0.59  thf(t152_zfmisc_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.21/0.59  thf('82', plain,
% 0.21/0.59      (![X13 : $i, X14 : $i]: ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.21/0.59      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.21/0.59  thf('83', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.59      inference('sup-', [status(thm)], ['81', '82'])).
% 0.21/0.59  thf('84', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.59      inference('sup-', [status(thm)], ['80', '83'])).
% 0.21/0.59  thf(t69_xboole_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.59       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.21/0.59  thf('85', plain,
% 0.21/0.59      (![X6 : $i, X7 : $i]:
% 0.21/0.59         (~ (r1_xboole_0 @ X6 @ X7)
% 0.21/0.59          | ~ (r1_tarski @ X6 @ X7)
% 0.21/0.59          | (v1_xboole_0 @ X6))),
% 0.21/0.59      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.21/0.59  thf('86', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         ((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.59  thf('87', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.21/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.59  thf('88', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.59      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.59  thf('89', plain,
% 0.21/0.59      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.59        | (v1_xboole_0 @ sk_D)
% 0.21/0.59        | (zip_tseitin_1 @ sk_C_1 @ sk_B))),
% 0.21/0.59      inference('demod', [status(thm)], ['77', '79', '88'])).
% 0.21/0.59  thf('90', plain,
% 0.21/0.59      (![X51 : $i, X52 : $i]:
% 0.21/0.59         (((X51) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X51 @ X52))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.59  thf('91', plain, (((v1_xboole_0 @ sk_D) | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.59      inference('clc', [status(thm)], ['89', '90'])).
% 0.21/0.59  thf('92', plain,
% 0.21/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.59  thf('93', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.59  thf('94', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('95', plain,
% 0.21/0.59      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_D) = (k1_xboole_0)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['93', '94'])).
% 0.21/0.59  thf('96', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.59      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.59  thf('97', plain, (((sk_D) = (k1_xboole_0))),
% 0.21/0.59      inference('demod', [status(thm)], ['95', '96'])).
% 0.21/0.59  thf('98', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.59      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.59  thf('99', plain, ((v1_xboole_0 @ sk_B)),
% 0.21/0.59      inference('demod', [status(thm)], ['7', '97', '98'])).
% 0.21/0.59  thf('100', plain,
% 0.21/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.59  thf('101', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['99', '100'])).
% 0.21/0.59  thf('102', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('103', plain, ($false),
% 0.21/0.59      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 0.21/0.59  
% 0.21/0.59  % SZS output end Refutation
% 0.21/0.59  
% 0.21/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

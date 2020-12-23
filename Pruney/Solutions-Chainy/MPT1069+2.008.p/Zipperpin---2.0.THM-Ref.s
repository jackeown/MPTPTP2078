%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fVn5mrp3Aq

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:02 EST 2020

% Result     : Theorem 35.60s
% Output     : Refutation 35.60s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 354 expanded)
%              Number of leaves         :   62 ( 130 expanded)
%              Depth                    :   23
%              Number of atoms          : 1765 (6808 expanded)
%              Number of equality atoms :   79 ( 279 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

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
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( v5_relat_1 @ X39 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ sk_F @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('simplify_reflect+',[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ sk_F @ sk_B_2 ),
    inference(clc,[status(thm)],['6','16'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C_1 ) ) ),
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

thf('21',plain,(
    ! [X82: $i,X83: $i,X84: $i,X85: $i] :
      ( ( zip_tseitin_3 @ X82 @ X83 )
      | ~ ( v1_funct_1 @ X84 )
      | ~ ( v1_funct_2 @ X84 @ X83 @ X82 )
      | ~ ( m1_subset_1 @ X84 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X83 @ X82 ) ) )
      | ( zip_tseitin_2 @ X84 @ X85 @ X83 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X83 @ X82 @ X84 ) @ X85 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_2 @ sk_C_1 @ sk_D_1 ) @ X0 )
      | ( zip_tseitin_2 @ sk_D_1 @ X0 @ sk_B_2 )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B_2 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( zip_tseitin_3 @ sk_C_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( ( k2_relset_1 @ X49 @ X50 @ X48 )
        = ( k2_relat_1 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('25',plain,
    ( ( k2_relset_1 @ sk_B_2 @ sk_C_1 @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B_2 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 )
      | ( zip_tseitin_2 @ sk_D_1 @ X0 @ sk_B_2 )
      | ( zip_tseitin_3 @ sk_C_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['22','25','26','27'])).

thf('29',plain,
    ( ( zip_tseitin_3 @ sk_C_1 @ sk_B_2 )
    | ( zip_tseitin_2 @ sk_D_1 @ ( k2_relat_1 @ sk_D_1 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X77: $i,X78: $i,X79: $i] :
      ( ( v1_funct_2 @ X77 @ X79 @ X78 )
      | ~ ( zip_tseitin_2 @ X77 @ X78 @ X79 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('31',plain,
    ( ( zip_tseitin_3 @ sk_C_1 @ sk_B_2 )
    | ( v1_funct_2 @ sk_D_1 @ sk_B_2 @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( zip_tseitin_3 @ sk_C_1 @ sk_B_2 )
    | ( zip_tseitin_2 @ sk_D_1 @ ( k2_relat_1 @ sk_D_1 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('33',plain,(
    ! [X77: $i,X78: $i,X79: $i] :
      ( ( m1_subset_1 @ X77 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X79 @ X78 ) ) )
      | ~ ( zip_tseitin_2 @ X77 @ X78 @ X79 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('34',plain,
    ( ( zip_tseitin_3 @ sk_C_1 @ sk_B_2 )
    | ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ ( k2_relat_1 @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('35',plain,(
    ! [X73: $i,X74: $i,X75: $i,X76: $i] :
      ( ~ ( r2_hidden @ X73 @ X74 )
      | ( X75 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X76 )
      | ~ ( v1_funct_2 @ X76 @ X74 @ X75 )
      | ~ ( m1_subset_1 @ X76 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X74 @ X75 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X76 @ X73 ) @ X75 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_C_1 @ sk_B_2 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k2_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B_2 @ ( k2_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( ( k2_relat_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_C_1 @ sk_B_2 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k2_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B_2 @ ( k2_relat_1 @ sk_D_1 ) )
      | ( ( k2_relat_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_C_1 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( ( k2_relat_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k2_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_3 @ sk_C_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k2_relat_1 @ sk_D_1 ) )
      | ( ( k2_relat_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( zip_tseitin_3 @ sk_C_1 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( zip_tseitin_3 @ sk_C_1 @ sk_B_2 )
    | ( ( k2_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_F ) @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['17','40'])).

thf('42',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_2 @ sk_C_1 @ sk_D_1 ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('44',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( ( k1_relset_1 @ X46 @ X47 @ X45 )
        = ( k1_relat_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('45',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_2 @ sk_C_1 @ sk_D_1 ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,
    ( ( k2_relset_1 @ sk_B_2 @ sk_C_1 @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('48',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('49',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( zip_tseitin_3 @ sk_C_1 @ sk_B_2 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['41','50'])).

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
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( r2_hidden @ X54 @ ( k1_relat_1 @ X55 ) )
      | ( ( k7_partfun1 @ X56 @ X55 @ X54 )
        = ( k1_funct_1 @ X55 @ X54 ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v5_relat_1 @ X55 @ X56 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_C_1 @ sk_B_2 )
      | ( ( k2_relat_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('55',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v1_relat_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('56',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_C_1 @ sk_B_2 )
      | ( ( k2_relat_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['53','56','57'])).

thf('59',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) ) )
    | ( ( k2_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( zip_tseitin_3 @ sk_C_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['3','58'])).

thf('60',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_2 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_F @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('63',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C_1 ) ) ),
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
    ! [X57: $i,X58: $i,X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_funct_2 @ X57 @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X59 ) ) )
      | ~ ( m1_subset_1 @ X60 @ X58 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X58 @ X59 @ X62 @ X57 @ X61 ) @ X60 )
        = ( k1_funct_1 @ X61 @ ( k1_funct_1 @ X57 @ X60 ) ) )
      | ( X58 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X58 @ X59 @ X57 ) @ ( k1_relset_1 @ X59 @ X62 @ X61 ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X62 ) ) )
      | ~ ( v1_funct_1 @ X61 )
      | ( v1_xboole_0 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_2 @ sk_C_1 @ sk_D_1 ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B_2 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_2 @ sk_C_1 @ X1 @ sk_D_1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_1 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_2 )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B_2 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k2_relset_1 @ sk_B_2 @ sk_C_1 @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('67',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B_2 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B_2 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_2 @ sk_C_1 @ X1 @ sk_D_1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_1 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_2 @ sk_C_1 @ X1 @ sk_D_1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_1 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_2 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_2 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['62','71'])).

thf('73',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('74',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B_2 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_2 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_2 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_2 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['61','78'])).

thf('80',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D_1 @ sk_F ) ) ),
    inference(demod,[status(thm)],['60','79'])).

thf('81',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( zip_tseitin_3 @ sk_C_1 @ sk_B_2 ) ),
    inference('simplify_reflect-',[status(thm)],['59','80'])).

thf('82',plain,(
    ! [X80: $i,X81: $i] :
      ( ( X80 = k1_xboole_0 )
      | ~ ( zip_tseitin_3 @ X80 @ X81 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('83',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('84',plain,(
    ! [X30: $i] :
      ( ( ( k2_relat_1 @ X30 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X30 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('85',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v1_relat_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('88',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','88'])).

thf('90',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['89'])).

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

thf('91',plain,(
    ! [X63: $i,X64: $i,X65: $i,X66: $i] :
      ( ( zip_tseitin_0 @ X63 @ X64 @ X65 @ X66 )
      | ( r2_hidden @ X63 @ X66 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('92',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X32 @ ( k1_relat_1 @ X33 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X33 @ X32 ) @ ( k2_relat_1 @ X33 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X1 @ X3 @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( v5_relat_1 @ X39 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('96',plain,(
    v5_relat_1 @ sk_D_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['94','95'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('97',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v5_relat_1 @ X26 @ X27 )
      | ( r1_tarski @ ( k2_relat_1 @ X26 ) @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('98',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['86','87'])).

thf('100',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( zip_tseitin_0 @ X0 @ X2 @ X1 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['93','102'])).

thf('104',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['86','87'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X0 @ X2 @ X1 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ! [X63: $i,X64: $i,X65: $i,X66: $i] :
      ( ( zip_tseitin_0 @ X63 @ X64 @ X65 @ X66 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X64 @ X63 ) @ X65 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X0 @ X3 @ X2 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_0 @ X0 @ sk_D_1 @ sk_C_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ sk_D_1 @ sk_C_1 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(eq_fact,[status(thm)],['108'])).

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

thf('110',plain,(
    ! [X70: $i,X71: $i,X72: $i] :
      ( ( ( k1_relat_1 @ X71 )
       != X70 )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X71 @ X72 @ X70 ) @ X71 @ X72 @ X70 )
      | ( zip_tseitin_1 @ X71 @ X72 @ X70 )
      | ~ ( v1_funct_1 @ X71 )
      | ~ ( v1_relat_1 @ X71 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('111',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( v1_relat_1 @ X71 )
      | ~ ( v1_funct_1 @ X71 )
      | ( zip_tseitin_1 @ X71 @ X72 @ ( k1_relat_1 @ X71 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ X71 @ X72 @ ( k1_relat_1 @ X71 ) ) @ X71 @ X72 @ ( k1_relat_1 @ X71 ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ ( k1_relat_1 @ sk_D_1 ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['109','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['86','87'])).

thf('115',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X68 ) ) )
      | ~ ( zip_tseitin_1 @ X67 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('117',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('118',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X44 ) ) )
      | ( v1_xboole_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('119',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C_1 ) ) ),
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

thf('121',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( v1_xboole_0 @ X51 )
      | ( v1_xboole_0 @ X52 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_2 @ X53 @ X51 @ X52 )
      | ~ ( v1_xboole_0 @ X53 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc6_funct_2])).

thf('122',plain,
    ( ~ ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_funct_2 @ sk_D_1 @ sk_B_2 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B_2 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ~ ( v1_xboole_0 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('simplify_reflect+',[status(thm)],['14','15'])).

thf('129',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['119','129'])).

thf('131',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','130'])).

thf('132',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('133',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('135',plain,(
    $false ),
    inference(demod,[status(thm)],['0','133','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fVn5mrp3Aq
% 0.16/0.37  % Computer   : n009.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 19:46:56 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 35.60/35.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 35.60/35.84  % Solved by: fo/fo7.sh
% 35.60/35.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 35.60/35.84  % done 45989 iterations in 35.378s
% 35.60/35.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 35.60/35.84  % SZS output start Refutation
% 35.60/35.84  thf(sk_B_2_type, type, sk_B_2: $i).
% 35.60/35.84  thf(sk_D_1_type, type, sk_D_1: $i).
% 35.60/35.84  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 35.60/35.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 35.60/35.84  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 35.60/35.84  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 35.60/35.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 35.60/35.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 35.60/35.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 35.60/35.84  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 35.60/35.84  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 35.60/35.84  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 35.60/35.84  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 35.60/35.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 35.60/35.84  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 35.60/35.84  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 35.60/35.84  thf(sk_E_type, type, sk_E: $i).
% 35.60/35.84  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 35.60/35.84  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 35.60/35.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 35.60/35.84  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 35.60/35.84  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 35.60/35.84  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 35.60/35.84  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 35.60/35.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 35.60/35.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 35.60/35.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 35.60/35.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 35.60/35.84  thf(sk_C_1_type, type, sk_C_1: $i).
% 35.60/35.84  thf(sk_A_type, type, sk_A: $i).
% 35.60/35.84  thf(sk_F_type, type, sk_F: $i).
% 35.60/35.84  thf(t186_funct_2, conjecture,
% 35.60/35.84    (![A:$i,B:$i,C:$i]:
% 35.60/35.84     ( ( ~( v1_xboole_0 @ C ) ) =>
% 35.60/35.84       ( ![D:$i]:
% 35.60/35.84         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 35.60/35.84             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 35.60/35.84           ( ![E:$i]:
% 35.60/35.84             ( ( ( v1_funct_1 @ E ) & 
% 35.60/35.84                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 35.60/35.84               ( ![F:$i]:
% 35.60/35.84                 ( ( m1_subset_1 @ F @ B ) =>
% 35.60/35.84                   ( ( r1_tarski @
% 35.60/35.84                       ( k2_relset_1 @ B @ C @ D ) @ 
% 35.60/35.84                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 35.60/35.84                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 35.60/35.84                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 35.60/35.84                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 35.60/35.84  thf(zf_stmt_0, negated_conjecture,
% 35.60/35.84    (~( ![A:$i,B:$i,C:$i]:
% 35.60/35.84        ( ( ~( v1_xboole_0 @ C ) ) =>
% 35.60/35.84          ( ![D:$i]:
% 35.60/35.84            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 35.60/35.84                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 35.60/35.84              ( ![E:$i]:
% 35.60/35.84                ( ( ( v1_funct_1 @ E ) & 
% 35.60/35.84                    ( m1_subset_1 @
% 35.60/35.84                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 35.60/35.84                  ( ![F:$i]:
% 35.60/35.84                    ( ( m1_subset_1 @ F @ B ) =>
% 35.60/35.84                      ( ( r1_tarski @
% 35.60/35.84                          ( k2_relset_1 @ B @ C @ D ) @ 
% 35.60/35.84                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 35.60/35.84                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 35.60/35.84                          ( ( k1_funct_1 @
% 35.60/35.84                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 35.60/35.84                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 35.60/35.84    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 35.60/35.84  thf('0', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('1', plain,
% 35.60/35.84      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf(cc2_relset_1, axiom,
% 35.60/35.84    (![A:$i,B:$i,C:$i]:
% 35.60/35.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 35.60/35.84       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 35.60/35.84  thf('2', plain,
% 35.60/35.84      (![X39 : $i, X40 : $i, X41 : $i]:
% 35.60/35.84         ((v5_relat_1 @ X39 @ X41)
% 35.60/35.84          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 35.60/35.84      inference('cnf', [status(esa)], [cc2_relset_1])).
% 35.60/35.84  thf('3', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 35.60/35.84      inference('sup-', [status(thm)], ['1', '2'])).
% 35.60/35.84  thf('4', plain, ((m1_subset_1 @ sk_F @ sk_B_2)),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf(t2_subset, axiom,
% 35.60/35.84    (![A:$i,B:$i]:
% 35.60/35.84     ( ( m1_subset_1 @ A @ B ) =>
% 35.60/35.84       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 35.60/35.84  thf('5', plain,
% 35.60/35.84      (![X18 : $i, X19 : $i]:
% 35.60/35.84         ((r2_hidden @ X18 @ X19)
% 35.60/35.84          | (v1_xboole_0 @ X19)
% 35.60/35.84          | ~ (m1_subset_1 @ X18 @ X19))),
% 35.60/35.84      inference('cnf', [status(esa)], [t2_subset])).
% 35.60/35.84  thf('6', plain, (((v1_xboole_0 @ sk_B_2) | (r2_hidden @ sk_F @ sk_B_2))),
% 35.60/35.84      inference('sup-', [status(thm)], ['4', '5'])).
% 35.60/35.84  thf(t7_xboole_0, axiom,
% 35.60/35.84    (![A:$i]:
% 35.60/35.84     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 35.60/35.84          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 35.60/35.84  thf('7', plain,
% 35.60/35.84      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X8) @ X8))),
% 35.60/35.84      inference('cnf', [status(esa)], [t7_xboole_0])).
% 35.60/35.84  thf(d1_xboole_0, axiom,
% 35.60/35.84    (![A:$i]:
% 35.60/35.84     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 35.60/35.84  thf('8', plain,
% 35.60/35.84      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 35.60/35.84      inference('cnf', [status(esa)], [d1_xboole_0])).
% 35.60/35.84  thf('9', plain,
% 35.60/35.84      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 35.60/35.84      inference('sup-', [status(thm)], ['7', '8'])).
% 35.60/35.84  thf('10', plain,
% 35.60/35.84      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 35.60/35.84      inference('sup-', [status(thm)], ['7', '8'])).
% 35.60/35.84  thf('11', plain,
% 35.60/35.84      (![X0 : $i, X1 : $i]:
% 35.60/35.84         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 35.60/35.84      inference('sup+', [status(thm)], ['9', '10'])).
% 35.60/35.84  thf('12', plain, (((sk_B_2) != (k1_xboole_0))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('13', plain,
% 35.60/35.84      (![X0 : $i]:
% 35.60/35.84         (((X0) != (k1_xboole_0))
% 35.60/35.84          | ~ (v1_xboole_0 @ X0)
% 35.60/35.84          | ~ (v1_xboole_0 @ sk_B_2))),
% 35.60/35.84      inference('sup-', [status(thm)], ['11', '12'])).
% 35.60/35.84  thf('14', plain,
% 35.60/35.84      ((~ (v1_xboole_0 @ sk_B_2) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 35.60/35.84      inference('simplify', [status(thm)], ['13'])).
% 35.60/35.84  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 35.60/35.84  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 35.60/35.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 35.60/35.84  thf('16', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 35.60/35.84      inference('simplify_reflect+', [status(thm)], ['14', '15'])).
% 35.60/35.84  thf('17', plain, ((r2_hidden @ sk_F @ sk_B_2)),
% 35.60/35.84      inference('clc', [status(thm)], ['6', '16'])).
% 35.60/35.84  thf(d10_xboole_0, axiom,
% 35.60/35.84    (![A:$i,B:$i]:
% 35.60/35.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 35.60/35.84  thf('18', plain,
% 35.60/35.84      (![X9 : $i, X10 : $i]: ((r1_tarski @ X9 @ X10) | ((X9) != (X10)))),
% 35.60/35.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 35.60/35.84  thf('19', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 35.60/35.84      inference('simplify', [status(thm)], ['18'])).
% 35.60/35.84  thf('20', plain,
% 35.60/35.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C_1)))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf(t8_funct_2, axiom,
% 35.60/35.84    (![A:$i,B:$i,C:$i,D:$i]:
% 35.60/35.84     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 35.60/35.84         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 35.60/35.84       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 35.60/35.84         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 35.60/35.84             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 35.60/35.84           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 35.60/35.84  thf(zf_stmt_1, type, zip_tseitin_3 : $i > $i > $o).
% 35.60/35.84  thf(zf_stmt_2, axiom,
% 35.60/35.84    (![B:$i,A:$i]:
% 35.60/35.84     ( ( zip_tseitin_3 @ B @ A ) =>
% 35.60/35.84       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 35.60/35.84  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 35.60/35.84  thf(zf_stmt_4, axiom,
% 35.60/35.84    (![D:$i,C:$i,A:$i]:
% 35.60/35.84     ( ( zip_tseitin_2 @ D @ C @ A ) =>
% 35.60/35.84       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 35.60/35.84         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 35.60/35.84  thf(zf_stmt_5, axiom,
% 35.60/35.84    (![A:$i,B:$i,C:$i,D:$i]:
% 35.60/35.84     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 35.60/35.84         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 35.60/35.84       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 35.60/35.84         ( ( zip_tseitin_3 @ B @ A ) | ( zip_tseitin_2 @ D @ C @ A ) ) ) ))).
% 35.60/35.84  thf('21', plain,
% 35.60/35.84      (![X82 : $i, X83 : $i, X84 : $i, X85 : $i]:
% 35.60/35.84         ((zip_tseitin_3 @ X82 @ X83)
% 35.60/35.84          | ~ (v1_funct_1 @ X84)
% 35.60/35.84          | ~ (v1_funct_2 @ X84 @ X83 @ X82)
% 35.60/35.84          | ~ (m1_subset_1 @ X84 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X83 @ X82)))
% 35.60/35.84          | (zip_tseitin_2 @ X84 @ X85 @ X83)
% 35.60/35.84          | ~ (r1_tarski @ (k2_relset_1 @ X83 @ X82 @ X84) @ X85))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_5])).
% 35.60/35.84  thf('22', plain,
% 35.60/35.84      (![X0 : $i]:
% 35.60/35.84         (~ (r1_tarski @ (k2_relset_1 @ sk_B_2 @ sk_C_1 @ sk_D_1) @ X0)
% 35.60/35.84          | (zip_tseitin_2 @ sk_D_1 @ X0 @ sk_B_2)
% 35.60/35.84          | ~ (v1_funct_2 @ sk_D_1 @ sk_B_2 @ sk_C_1)
% 35.60/35.84          | ~ (v1_funct_1 @ sk_D_1)
% 35.60/35.84          | (zip_tseitin_3 @ sk_C_1 @ sk_B_2))),
% 35.60/35.84      inference('sup-', [status(thm)], ['20', '21'])).
% 35.60/35.84  thf('23', plain,
% 35.60/35.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C_1)))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf(redefinition_k2_relset_1, axiom,
% 35.60/35.84    (![A:$i,B:$i,C:$i]:
% 35.60/35.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 35.60/35.84       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 35.60/35.84  thf('24', plain,
% 35.60/35.84      (![X48 : $i, X49 : $i, X50 : $i]:
% 35.60/35.84         (((k2_relset_1 @ X49 @ X50 @ X48) = (k2_relat_1 @ X48))
% 35.60/35.84          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50))))),
% 35.60/35.84      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 35.60/35.84  thf('25', plain,
% 35.60/35.84      (((k2_relset_1 @ sk_B_2 @ sk_C_1 @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 35.60/35.84      inference('sup-', [status(thm)], ['23', '24'])).
% 35.60/35.84  thf('26', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_2 @ sk_C_1)),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('27', plain, ((v1_funct_1 @ sk_D_1)),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('28', plain,
% 35.60/35.84      (![X0 : $i]:
% 35.60/35.84         (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0)
% 35.60/35.84          | (zip_tseitin_2 @ sk_D_1 @ X0 @ sk_B_2)
% 35.60/35.84          | (zip_tseitin_3 @ sk_C_1 @ sk_B_2))),
% 35.60/35.84      inference('demod', [status(thm)], ['22', '25', '26', '27'])).
% 35.60/35.84  thf('29', plain,
% 35.60/35.84      (((zip_tseitin_3 @ sk_C_1 @ sk_B_2)
% 35.60/35.84        | (zip_tseitin_2 @ sk_D_1 @ (k2_relat_1 @ sk_D_1) @ sk_B_2))),
% 35.60/35.84      inference('sup-', [status(thm)], ['19', '28'])).
% 35.60/35.84  thf('30', plain,
% 35.60/35.84      (![X77 : $i, X78 : $i, X79 : $i]:
% 35.60/35.84         ((v1_funct_2 @ X77 @ X79 @ X78) | ~ (zip_tseitin_2 @ X77 @ X78 @ X79))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_4])).
% 35.60/35.84  thf('31', plain,
% 35.60/35.84      (((zip_tseitin_3 @ sk_C_1 @ sk_B_2)
% 35.60/35.84        | (v1_funct_2 @ sk_D_1 @ sk_B_2 @ (k2_relat_1 @ sk_D_1)))),
% 35.60/35.84      inference('sup-', [status(thm)], ['29', '30'])).
% 35.60/35.84  thf('32', plain,
% 35.60/35.84      (((zip_tseitin_3 @ sk_C_1 @ sk_B_2)
% 35.60/35.84        | (zip_tseitin_2 @ sk_D_1 @ (k2_relat_1 @ sk_D_1) @ sk_B_2))),
% 35.60/35.84      inference('sup-', [status(thm)], ['19', '28'])).
% 35.60/35.84  thf('33', plain,
% 35.60/35.84      (![X77 : $i, X78 : $i, X79 : $i]:
% 35.60/35.84         ((m1_subset_1 @ X77 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X79 @ X78)))
% 35.60/35.84          | ~ (zip_tseitin_2 @ X77 @ X78 @ X79))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_4])).
% 35.60/35.84  thf('34', plain,
% 35.60/35.84      (((zip_tseitin_3 @ sk_C_1 @ sk_B_2)
% 35.60/35.84        | (m1_subset_1 @ sk_D_1 @ 
% 35.60/35.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ (k2_relat_1 @ sk_D_1)))))),
% 35.60/35.84      inference('sup-', [status(thm)], ['32', '33'])).
% 35.60/35.84  thf(t7_funct_2, axiom,
% 35.60/35.84    (![A:$i,B:$i,C:$i,D:$i]:
% 35.60/35.84     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 35.60/35.84         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 35.60/35.84       ( ( r2_hidden @ C @ A ) =>
% 35.60/35.84         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 35.60/35.84           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 35.60/35.84  thf('35', plain,
% 35.60/35.84      (![X73 : $i, X74 : $i, X75 : $i, X76 : $i]:
% 35.60/35.84         (~ (r2_hidden @ X73 @ X74)
% 35.60/35.84          | ((X75) = (k1_xboole_0))
% 35.60/35.84          | ~ (v1_funct_1 @ X76)
% 35.60/35.84          | ~ (v1_funct_2 @ X76 @ X74 @ X75)
% 35.60/35.84          | ~ (m1_subset_1 @ X76 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X74 @ X75)))
% 35.60/35.84          | (r2_hidden @ (k1_funct_1 @ X76 @ X73) @ X75))),
% 35.60/35.84      inference('cnf', [status(esa)], [t7_funct_2])).
% 35.60/35.84  thf('36', plain,
% 35.60/35.84      (![X0 : $i]:
% 35.60/35.84         ((zip_tseitin_3 @ sk_C_1 @ sk_B_2)
% 35.60/35.84          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k2_relat_1 @ sk_D_1))
% 35.60/35.84          | ~ (v1_funct_2 @ sk_D_1 @ sk_B_2 @ (k2_relat_1 @ sk_D_1))
% 35.60/35.84          | ~ (v1_funct_1 @ sk_D_1)
% 35.60/35.84          | ((k2_relat_1 @ sk_D_1) = (k1_xboole_0))
% 35.60/35.84          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 35.60/35.84      inference('sup-', [status(thm)], ['34', '35'])).
% 35.60/35.84  thf('37', plain, ((v1_funct_1 @ sk_D_1)),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('38', plain,
% 35.60/35.84      (![X0 : $i]:
% 35.60/35.84         ((zip_tseitin_3 @ sk_C_1 @ sk_B_2)
% 35.60/35.84          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k2_relat_1 @ sk_D_1))
% 35.60/35.84          | ~ (v1_funct_2 @ sk_D_1 @ sk_B_2 @ (k2_relat_1 @ sk_D_1))
% 35.60/35.84          | ((k2_relat_1 @ sk_D_1) = (k1_xboole_0))
% 35.60/35.84          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 35.60/35.84      inference('demod', [status(thm)], ['36', '37'])).
% 35.60/35.84  thf('39', plain,
% 35.60/35.84      (![X0 : $i]:
% 35.60/35.84         ((zip_tseitin_3 @ sk_C_1 @ sk_B_2)
% 35.60/35.84          | ~ (r2_hidden @ X0 @ sk_B_2)
% 35.60/35.84          | ((k2_relat_1 @ sk_D_1) = (k1_xboole_0))
% 35.60/35.84          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k2_relat_1 @ sk_D_1))
% 35.60/35.84          | (zip_tseitin_3 @ sk_C_1 @ sk_B_2))),
% 35.60/35.84      inference('sup-', [status(thm)], ['31', '38'])).
% 35.60/35.84  thf('40', plain,
% 35.60/35.84      (![X0 : $i]:
% 35.60/35.84         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k2_relat_1 @ sk_D_1))
% 35.60/35.84          | ((k2_relat_1 @ sk_D_1) = (k1_xboole_0))
% 35.60/35.84          | ~ (r2_hidden @ X0 @ sk_B_2)
% 35.60/35.84          | (zip_tseitin_3 @ sk_C_1 @ sk_B_2))),
% 35.60/35.84      inference('simplify', [status(thm)], ['39'])).
% 35.60/35.84  thf('41', plain,
% 35.60/35.84      (((zip_tseitin_3 @ sk_C_1 @ sk_B_2)
% 35.60/35.84        | ((k2_relat_1 @ sk_D_1) = (k1_xboole_0))
% 35.60/35.84        | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_F) @ (k2_relat_1 @ sk_D_1)))),
% 35.60/35.84      inference('sup-', [status(thm)], ['17', '40'])).
% 35.60/35.84  thf('42', plain,
% 35.60/35.84      ((r1_tarski @ (k2_relset_1 @ sk_B_2 @ sk_C_1 @ sk_D_1) @ 
% 35.60/35.84        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('43', plain,
% 35.60/35.84      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf(redefinition_k1_relset_1, axiom,
% 35.60/35.84    (![A:$i,B:$i,C:$i]:
% 35.60/35.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 35.60/35.84       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 35.60/35.84  thf('44', plain,
% 35.60/35.84      (![X45 : $i, X46 : $i, X47 : $i]:
% 35.60/35.84         (((k1_relset_1 @ X46 @ X47 @ X45) = (k1_relat_1 @ X45))
% 35.60/35.84          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47))))),
% 35.60/35.84      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 35.60/35.84  thf('45', plain,
% 35.60/35.84      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 35.60/35.84      inference('sup-', [status(thm)], ['43', '44'])).
% 35.60/35.84  thf('46', plain,
% 35.60/35.84      ((r1_tarski @ (k2_relset_1 @ sk_B_2 @ sk_C_1 @ sk_D_1) @ 
% 35.60/35.84        (k1_relat_1 @ sk_E))),
% 35.60/35.84      inference('demod', [status(thm)], ['42', '45'])).
% 35.60/35.84  thf('47', plain,
% 35.60/35.84      (((k2_relset_1 @ sk_B_2 @ sk_C_1 @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 35.60/35.84      inference('sup-', [status(thm)], ['23', '24'])).
% 35.60/35.84  thf('48', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ (k1_relat_1 @ sk_E))),
% 35.60/35.84      inference('demod', [status(thm)], ['46', '47'])).
% 35.60/35.84  thf(d3_tarski, axiom,
% 35.60/35.84    (![A:$i,B:$i]:
% 35.60/35.84     ( ( r1_tarski @ A @ B ) <=>
% 35.60/35.84       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 35.60/35.84  thf('49', plain,
% 35.60/35.84      (![X3 : $i, X4 : $i, X5 : $i]:
% 35.60/35.84         (~ (r2_hidden @ X3 @ X4)
% 35.60/35.84          | (r2_hidden @ X3 @ X5)
% 35.60/35.84          | ~ (r1_tarski @ X4 @ X5))),
% 35.60/35.84      inference('cnf', [status(esa)], [d3_tarski])).
% 35.60/35.84  thf('50', plain,
% 35.60/35.84      (![X0 : $i]:
% 35.60/35.84         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 35.60/35.84          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1)))),
% 35.60/35.84      inference('sup-', [status(thm)], ['48', '49'])).
% 35.60/35.84  thf('51', plain,
% 35.60/35.84      ((((k2_relat_1 @ sk_D_1) = (k1_xboole_0))
% 35.60/35.84        | (zip_tseitin_3 @ sk_C_1 @ sk_B_2)
% 35.60/35.84        | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 35.60/35.84      inference('sup-', [status(thm)], ['41', '50'])).
% 35.60/35.84  thf(d8_partfun1, axiom,
% 35.60/35.84    (![A:$i,B:$i]:
% 35.60/35.84     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 35.60/35.84       ( ![C:$i]:
% 35.60/35.84         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 35.60/35.84           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 35.60/35.84  thf('52', plain,
% 35.60/35.84      (![X54 : $i, X55 : $i, X56 : $i]:
% 35.60/35.84         (~ (r2_hidden @ X54 @ (k1_relat_1 @ X55))
% 35.60/35.84          | ((k7_partfun1 @ X56 @ X55 @ X54) = (k1_funct_1 @ X55 @ X54))
% 35.60/35.84          | ~ (v1_funct_1 @ X55)
% 35.60/35.84          | ~ (v5_relat_1 @ X55 @ X56)
% 35.60/35.84          | ~ (v1_relat_1 @ X55))),
% 35.60/35.84      inference('cnf', [status(esa)], [d8_partfun1])).
% 35.60/35.84  thf('53', plain,
% 35.60/35.84      (![X0 : $i]:
% 35.60/35.84         ((zip_tseitin_3 @ sk_C_1 @ sk_B_2)
% 35.60/35.84          | ((k2_relat_1 @ sk_D_1) = (k1_xboole_0))
% 35.60/35.84          | ~ (v1_relat_1 @ sk_E)
% 35.60/35.84          | ~ (v5_relat_1 @ sk_E @ X0)
% 35.60/35.84          | ~ (v1_funct_1 @ sk_E)
% 35.60/35.84          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F))
% 35.60/35.84              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F))))),
% 35.60/35.84      inference('sup-', [status(thm)], ['51', '52'])).
% 35.60/35.84  thf('54', plain,
% 35.60/35.84      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf(cc1_relset_1, axiom,
% 35.60/35.84    (![A:$i,B:$i,C:$i]:
% 35.60/35.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 35.60/35.84       ( v1_relat_1 @ C ) ))).
% 35.60/35.84  thf('55', plain,
% 35.60/35.84      (![X36 : $i, X37 : $i, X38 : $i]:
% 35.60/35.84         ((v1_relat_1 @ X36)
% 35.60/35.84          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 35.60/35.84      inference('cnf', [status(esa)], [cc1_relset_1])).
% 35.60/35.84  thf('56', plain, ((v1_relat_1 @ sk_E)),
% 35.60/35.84      inference('sup-', [status(thm)], ['54', '55'])).
% 35.60/35.84  thf('57', plain, ((v1_funct_1 @ sk_E)),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('58', plain,
% 35.60/35.84      (![X0 : $i]:
% 35.60/35.84         ((zip_tseitin_3 @ sk_C_1 @ sk_B_2)
% 35.60/35.84          | ((k2_relat_1 @ sk_D_1) = (k1_xboole_0))
% 35.60/35.84          | ~ (v5_relat_1 @ sk_E @ X0)
% 35.60/35.84          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F))
% 35.60/35.84              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F))))),
% 35.60/35.84      inference('demod', [status(thm)], ['53', '56', '57'])).
% 35.60/35.84  thf('59', plain,
% 35.60/35.84      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F))
% 35.60/35.84          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F)))
% 35.60/35.84        | ((k2_relat_1 @ sk_D_1) = (k1_xboole_0))
% 35.60/35.84        | (zip_tseitin_3 @ sk_C_1 @ sk_B_2))),
% 35.60/35.84      inference('sup-', [status(thm)], ['3', '58'])).
% 35.60/35.84  thf('60', plain,
% 35.60/35.84      (((k1_funct_1 @ (k8_funct_2 @ sk_B_2 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_E) @ 
% 35.60/35.84         sk_F) != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F)))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('61', plain, ((m1_subset_1 @ sk_F @ sk_B_2)),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('62', plain,
% 35.60/35.84      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 35.60/35.84      inference('sup-', [status(thm)], ['43', '44'])).
% 35.60/35.84  thf('63', plain,
% 35.60/35.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C_1)))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf(t185_funct_2, axiom,
% 35.60/35.84    (![A:$i,B:$i,C:$i]:
% 35.60/35.84     ( ( ~( v1_xboole_0 @ C ) ) =>
% 35.60/35.84       ( ![D:$i]:
% 35.60/35.84         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 35.60/35.84             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 35.60/35.84           ( ![E:$i]:
% 35.60/35.84             ( ( ( v1_funct_1 @ E ) & 
% 35.60/35.84                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 35.60/35.84               ( ![F:$i]:
% 35.60/35.84                 ( ( m1_subset_1 @ F @ B ) =>
% 35.60/35.84                   ( ( r1_tarski @
% 35.60/35.84                       ( k2_relset_1 @ B @ C @ D ) @ 
% 35.60/35.84                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 35.60/35.84                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 35.60/35.84                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 35.60/35.84                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 35.60/35.84  thf('64', plain,
% 35.60/35.84      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 35.60/35.84         (~ (v1_funct_1 @ X57)
% 35.60/35.84          | ~ (v1_funct_2 @ X57 @ X58 @ X59)
% 35.60/35.84          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X59)))
% 35.60/35.84          | ~ (m1_subset_1 @ X60 @ X58)
% 35.60/35.84          | ((k1_funct_1 @ (k8_funct_2 @ X58 @ X59 @ X62 @ X57 @ X61) @ X60)
% 35.60/35.84              = (k1_funct_1 @ X61 @ (k1_funct_1 @ X57 @ X60)))
% 35.60/35.84          | ((X58) = (k1_xboole_0))
% 35.60/35.84          | ~ (r1_tarski @ (k2_relset_1 @ X58 @ X59 @ X57) @ 
% 35.60/35.84               (k1_relset_1 @ X59 @ X62 @ X61))
% 35.60/35.84          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X62)))
% 35.60/35.84          | ~ (v1_funct_1 @ X61)
% 35.60/35.84          | (v1_xboole_0 @ X59))),
% 35.60/35.84      inference('cnf', [status(esa)], [t185_funct_2])).
% 35.60/35.84  thf('65', plain,
% 35.60/35.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.60/35.84         ((v1_xboole_0 @ sk_C_1)
% 35.60/35.84          | ~ (v1_funct_1 @ X0)
% 35.60/35.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 35.60/35.84          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_2 @ sk_C_1 @ sk_D_1) @ 
% 35.60/35.84               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 35.60/35.84          | ((sk_B_2) = (k1_xboole_0))
% 35.60/35.84          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_2 @ sk_C_1 @ X1 @ sk_D_1 @ X0) @ 
% 35.60/35.84              X2) = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_1 @ X2)))
% 35.60/35.84          | ~ (m1_subset_1 @ X2 @ sk_B_2)
% 35.60/35.84          | ~ (v1_funct_2 @ sk_D_1 @ sk_B_2 @ sk_C_1)
% 35.60/35.84          | ~ (v1_funct_1 @ sk_D_1))),
% 35.60/35.84      inference('sup-', [status(thm)], ['63', '64'])).
% 35.60/35.84  thf('66', plain,
% 35.60/35.84      (((k2_relset_1 @ sk_B_2 @ sk_C_1 @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 35.60/35.84      inference('sup-', [status(thm)], ['23', '24'])).
% 35.60/35.84  thf('67', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_2 @ sk_C_1)),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('68', plain, ((v1_funct_1 @ sk_D_1)),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('69', plain,
% 35.60/35.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.60/35.84         ((v1_xboole_0 @ sk_C_1)
% 35.60/35.84          | ~ (v1_funct_1 @ X0)
% 35.60/35.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 35.60/35.84          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ 
% 35.60/35.84               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 35.60/35.84          | ((sk_B_2) = (k1_xboole_0))
% 35.60/35.84          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_2 @ sk_C_1 @ X1 @ sk_D_1 @ X0) @ 
% 35.60/35.84              X2) = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_1 @ X2)))
% 35.60/35.84          | ~ (m1_subset_1 @ X2 @ sk_B_2))),
% 35.60/35.84      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 35.60/35.84  thf('70', plain, (((sk_B_2) != (k1_xboole_0))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('71', plain,
% 35.60/35.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.60/35.84         ((v1_xboole_0 @ sk_C_1)
% 35.60/35.84          | ~ (v1_funct_1 @ X0)
% 35.60/35.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 35.60/35.84          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ 
% 35.60/35.84               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 35.60/35.84          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_2 @ sk_C_1 @ X1 @ sk_D_1 @ X0) @ 
% 35.60/35.84              X2) = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_1 @ X2)))
% 35.60/35.84          | ~ (m1_subset_1 @ X2 @ sk_B_2))),
% 35.60/35.84      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 35.60/35.84  thf('72', plain,
% 35.60/35.84      (![X0 : $i]:
% 35.60/35.84         (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ (k1_relat_1 @ sk_E))
% 35.60/35.84          | ~ (m1_subset_1 @ X0 @ sk_B_2)
% 35.60/35.84          | ((k1_funct_1 @ 
% 35.60/35.84              (k8_funct_2 @ sk_B_2 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_E) @ X0)
% 35.60/35.84              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_1 @ X0)))
% 35.60/35.84          | ~ (m1_subset_1 @ sk_E @ 
% 35.60/35.84               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 35.60/35.84          | ~ (v1_funct_1 @ sk_E)
% 35.60/35.84          | (v1_xboole_0 @ sk_C_1))),
% 35.60/35.84      inference('sup-', [status(thm)], ['62', '71'])).
% 35.60/35.84  thf('73', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ (k1_relat_1 @ sk_E))),
% 35.60/35.84      inference('demod', [status(thm)], ['46', '47'])).
% 35.60/35.84  thf('74', plain,
% 35.60/35.84      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('75', plain, ((v1_funct_1 @ sk_E)),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('76', plain,
% 35.60/35.84      (![X0 : $i]:
% 35.60/35.84         (~ (m1_subset_1 @ X0 @ sk_B_2)
% 35.60/35.84          | ((k1_funct_1 @ 
% 35.60/35.84              (k8_funct_2 @ sk_B_2 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_E) @ X0)
% 35.60/35.84              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_1 @ X0)))
% 35.60/35.84          | (v1_xboole_0 @ sk_C_1))),
% 35.60/35.84      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 35.60/35.84  thf('77', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('78', plain,
% 35.60/35.84      (![X0 : $i]:
% 35.60/35.84         (((k1_funct_1 @ 
% 35.60/35.84            (k8_funct_2 @ sk_B_2 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_E) @ X0)
% 35.60/35.84            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_1 @ X0)))
% 35.60/35.84          | ~ (m1_subset_1 @ X0 @ sk_B_2))),
% 35.60/35.84      inference('clc', [status(thm)], ['76', '77'])).
% 35.60/35.84  thf('79', plain,
% 35.60/35.84      (((k1_funct_1 @ (k8_funct_2 @ sk_B_2 @ sk_C_1 @ sk_A @ sk_D_1 @ sk_E) @ 
% 35.60/35.84         sk_F) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F)))),
% 35.60/35.84      inference('sup-', [status(thm)], ['61', '78'])).
% 35.60/35.84  thf('80', plain,
% 35.60/35.84      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F))
% 35.60/35.84         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D_1 @ sk_F)))),
% 35.60/35.84      inference('demod', [status(thm)], ['60', '79'])).
% 35.60/35.84  thf('81', plain,
% 35.60/35.84      ((((k2_relat_1 @ sk_D_1) = (k1_xboole_0))
% 35.60/35.84        | (zip_tseitin_3 @ sk_C_1 @ sk_B_2))),
% 35.60/35.84      inference('simplify_reflect-', [status(thm)], ['59', '80'])).
% 35.60/35.84  thf('82', plain,
% 35.60/35.84      (![X80 : $i, X81 : $i]:
% 35.60/35.84         (((X80) = (k1_xboole_0)) | ~ (zip_tseitin_3 @ X80 @ X81))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 35.60/35.84  thf('83', plain,
% 35.60/35.84      ((((k2_relat_1 @ sk_D_1) = (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 35.60/35.84      inference('sup-', [status(thm)], ['81', '82'])).
% 35.60/35.84  thf(t65_relat_1, axiom,
% 35.60/35.84    (![A:$i]:
% 35.60/35.84     ( ( v1_relat_1 @ A ) =>
% 35.60/35.84       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 35.60/35.84         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 35.60/35.84  thf('84', plain,
% 35.60/35.84      (![X30 : $i]:
% 35.60/35.84         (((k2_relat_1 @ X30) != (k1_xboole_0))
% 35.60/35.84          | ((k1_relat_1 @ X30) = (k1_xboole_0))
% 35.60/35.84          | ~ (v1_relat_1 @ X30))),
% 35.60/35.84      inference('cnf', [status(esa)], [t65_relat_1])).
% 35.60/35.84  thf('85', plain,
% 35.60/35.84      ((((k1_xboole_0) != (k1_xboole_0))
% 35.60/35.84        | ((sk_C_1) = (k1_xboole_0))
% 35.60/35.84        | ~ (v1_relat_1 @ sk_D_1)
% 35.60/35.84        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 35.60/35.84      inference('sup-', [status(thm)], ['83', '84'])).
% 35.60/35.84  thf('86', plain,
% 35.60/35.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C_1)))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('87', plain,
% 35.60/35.84      (![X36 : $i, X37 : $i, X38 : $i]:
% 35.60/35.84         ((v1_relat_1 @ X36)
% 35.60/35.84          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 35.60/35.84      inference('cnf', [status(esa)], [cc1_relset_1])).
% 35.60/35.84  thf('88', plain, ((v1_relat_1 @ sk_D_1)),
% 35.60/35.84      inference('sup-', [status(thm)], ['86', '87'])).
% 35.60/35.84  thf('89', plain,
% 35.60/35.84      ((((k1_xboole_0) != (k1_xboole_0))
% 35.60/35.84        | ((sk_C_1) = (k1_xboole_0))
% 35.60/35.84        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 35.60/35.84      inference('demod', [status(thm)], ['85', '88'])).
% 35.60/35.84  thf('90', plain,
% 35.60/35.84      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 35.60/35.84      inference('simplify', [status(thm)], ['89'])).
% 35.60/35.84  thf(t5_funct_2, axiom,
% 35.60/35.84    (![A:$i,B:$i,C:$i]:
% 35.60/35.84     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 35.60/35.84       ( ( ( ![D:$i]:
% 35.60/35.84             ( ( r2_hidden @ D @ A ) =>
% 35.60/35.84               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 35.60/35.84           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 35.60/35.84         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 35.60/35.84           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 35.60/35.84  thf(zf_stmt_6, axiom,
% 35.60/35.84    (![D:$i,C:$i,B:$i,A:$i]:
% 35.60/35.84     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 35.60/35.84       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 35.60/35.84  thf('91', plain,
% 35.60/35.84      (![X63 : $i, X64 : $i, X65 : $i, X66 : $i]:
% 35.60/35.84         ((zip_tseitin_0 @ X63 @ X64 @ X65 @ X66) | (r2_hidden @ X63 @ X66))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_6])).
% 35.60/35.84  thf(t12_funct_1, axiom,
% 35.60/35.84    (![A:$i,B:$i]:
% 35.60/35.84     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 35.60/35.84       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 35.60/35.84         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 35.60/35.84  thf('92', plain,
% 35.60/35.84      (![X32 : $i, X33 : $i]:
% 35.60/35.84         (~ (r2_hidden @ X32 @ (k1_relat_1 @ X33))
% 35.60/35.84          | (r2_hidden @ (k1_funct_1 @ X33 @ X32) @ (k2_relat_1 @ X33))
% 35.60/35.84          | ~ (v1_funct_1 @ X33)
% 35.60/35.84          | ~ (v1_relat_1 @ X33))),
% 35.60/35.84      inference('cnf', [status(esa)], [t12_funct_1])).
% 35.60/35.84  thf('93', plain,
% 35.60/35.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 35.60/35.84         ((zip_tseitin_0 @ X1 @ X3 @ X2 @ (k1_relat_1 @ X0))
% 35.60/35.84          | ~ (v1_relat_1 @ X0)
% 35.60/35.84          | ~ (v1_funct_1 @ X0)
% 35.60/35.84          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ (k2_relat_1 @ X0)))),
% 35.60/35.84      inference('sup-', [status(thm)], ['91', '92'])).
% 35.60/35.84  thf('94', plain,
% 35.60/35.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C_1)))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('95', plain,
% 35.60/35.84      (![X39 : $i, X40 : $i, X41 : $i]:
% 35.60/35.84         ((v5_relat_1 @ X39 @ X41)
% 35.60/35.84          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 35.60/35.84      inference('cnf', [status(esa)], [cc2_relset_1])).
% 35.60/35.84  thf('96', plain, ((v5_relat_1 @ sk_D_1 @ sk_C_1)),
% 35.60/35.84      inference('sup-', [status(thm)], ['94', '95'])).
% 35.60/35.84  thf(d19_relat_1, axiom,
% 35.60/35.84    (![A:$i,B:$i]:
% 35.60/35.84     ( ( v1_relat_1 @ B ) =>
% 35.60/35.84       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 35.60/35.84  thf('97', plain,
% 35.60/35.84      (![X26 : $i, X27 : $i]:
% 35.60/35.84         (~ (v5_relat_1 @ X26 @ X27)
% 35.60/35.84          | (r1_tarski @ (k2_relat_1 @ X26) @ X27)
% 35.60/35.84          | ~ (v1_relat_1 @ X26))),
% 35.60/35.84      inference('cnf', [status(esa)], [d19_relat_1])).
% 35.60/35.84  thf('98', plain,
% 35.60/35.84      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_C_1))),
% 35.60/35.84      inference('sup-', [status(thm)], ['96', '97'])).
% 35.60/35.84  thf('99', plain, ((v1_relat_1 @ sk_D_1)),
% 35.60/35.84      inference('sup-', [status(thm)], ['86', '87'])).
% 35.60/35.84  thf('100', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_C_1)),
% 35.60/35.84      inference('demod', [status(thm)], ['98', '99'])).
% 35.60/35.84  thf('101', plain,
% 35.60/35.84      (![X3 : $i, X4 : $i, X5 : $i]:
% 35.60/35.84         (~ (r2_hidden @ X3 @ X4)
% 35.60/35.84          | (r2_hidden @ X3 @ X5)
% 35.60/35.84          | ~ (r1_tarski @ X4 @ X5))),
% 35.60/35.84      inference('cnf', [status(esa)], [d3_tarski])).
% 35.60/35.84  thf('102', plain,
% 35.60/35.84      (![X0 : $i]:
% 35.60/35.84         ((r2_hidden @ X0 @ sk_C_1)
% 35.60/35.84          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1)))),
% 35.60/35.84      inference('sup-', [status(thm)], ['100', '101'])).
% 35.60/35.84  thf('103', plain,
% 35.60/35.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.60/35.84         (~ (v1_funct_1 @ sk_D_1)
% 35.60/35.84          | ~ (v1_relat_1 @ sk_D_1)
% 35.60/35.84          | (zip_tseitin_0 @ X0 @ X2 @ X1 @ (k1_relat_1 @ sk_D_1))
% 35.60/35.84          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ sk_C_1))),
% 35.60/35.84      inference('sup-', [status(thm)], ['93', '102'])).
% 35.60/35.84  thf('104', plain, ((v1_funct_1 @ sk_D_1)),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('105', plain, ((v1_relat_1 @ sk_D_1)),
% 35.60/35.84      inference('sup-', [status(thm)], ['86', '87'])).
% 35.60/35.84  thf('106', plain,
% 35.60/35.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.60/35.84         ((zip_tseitin_0 @ X0 @ X2 @ X1 @ (k1_relat_1 @ sk_D_1))
% 35.60/35.84          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ sk_C_1))),
% 35.60/35.84      inference('demod', [status(thm)], ['103', '104', '105'])).
% 35.60/35.84  thf('107', plain,
% 35.60/35.84      (![X63 : $i, X64 : $i, X65 : $i, X66 : $i]:
% 35.60/35.84         ((zip_tseitin_0 @ X63 @ X64 @ X65 @ X66)
% 35.60/35.84          | ~ (r2_hidden @ (k1_funct_1 @ X64 @ X63) @ X65))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_6])).
% 35.60/35.84  thf('108', plain,
% 35.60/35.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 35.60/35.84         ((zip_tseitin_0 @ X0 @ X3 @ X2 @ (k1_relat_1 @ sk_D_1))
% 35.60/35.84          | (zip_tseitin_0 @ X0 @ sk_D_1 @ sk_C_1 @ X1))),
% 35.60/35.84      inference('sup-', [status(thm)], ['106', '107'])).
% 35.60/35.84  thf('109', plain,
% 35.60/35.84      (![X0 : $i]:
% 35.60/35.84         (zip_tseitin_0 @ X0 @ sk_D_1 @ sk_C_1 @ (k1_relat_1 @ sk_D_1))),
% 35.60/35.84      inference('eq_fact', [status(thm)], ['108'])).
% 35.60/35.84  thf(zf_stmt_7, type, zip_tseitin_1 : $i > $i > $i > $o).
% 35.60/35.84  thf(zf_stmt_8, axiom,
% 35.60/35.84    (![C:$i,B:$i,A:$i]:
% 35.60/35.84     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 35.60/35.84       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 35.60/35.84         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 35.60/35.84  thf(zf_stmt_9, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 35.60/35.84  thf(zf_stmt_10, axiom,
% 35.60/35.84    (![A:$i,B:$i,C:$i]:
% 35.60/35.84     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 35.60/35.84       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 35.60/35.84           ( ![D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) =>
% 35.60/35.84         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 35.60/35.84  thf('110', plain,
% 35.60/35.84      (![X70 : $i, X71 : $i, X72 : $i]:
% 35.60/35.84         (((k1_relat_1 @ X71) != (X70))
% 35.60/35.84          | ~ (zip_tseitin_0 @ (sk_D @ X71 @ X72 @ X70) @ X71 @ X72 @ X70)
% 35.60/35.84          | (zip_tseitin_1 @ X71 @ X72 @ X70)
% 35.60/35.84          | ~ (v1_funct_1 @ X71)
% 35.60/35.84          | ~ (v1_relat_1 @ X71))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_10])).
% 35.60/35.84  thf('111', plain,
% 35.60/35.84      (![X71 : $i, X72 : $i]:
% 35.60/35.84         (~ (v1_relat_1 @ X71)
% 35.60/35.84          | ~ (v1_funct_1 @ X71)
% 35.60/35.84          | (zip_tseitin_1 @ X71 @ X72 @ (k1_relat_1 @ X71))
% 35.60/35.84          | ~ (zip_tseitin_0 @ (sk_D @ X71 @ X72 @ (k1_relat_1 @ X71)) @ X71 @ 
% 35.60/35.84               X72 @ (k1_relat_1 @ X71)))),
% 35.60/35.84      inference('simplify', [status(thm)], ['110'])).
% 35.60/35.84  thf('112', plain,
% 35.60/35.84      (((zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ (k1_relat_1 @ sk_D_1))
% 35.60/35.84        | ~ (v1_funct_1 @ sk_D_1)
% 35.60/35.84        | ~ (v1_relat_1 @ sk_D_1))),
% 35.60/35.84      inference('sup-', [status(thm)], ['109', '111'])).
% 35.60/35.84  thf('113', plain, ((v1_funct_1 @ sk_D_1)),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('114', plain, ((v1_relat_1 @ sk_D_1)),
% 35.60/35.84      inference('sup-', [status(thm)], ['86', '87'])).
% 35.60/35.84  thf('115', plain,
% 35.60/35.84      ((zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ (k1_relat_1 @ sk_D_1))),
% 35.60/35.84      inference('demod', [status(thm)], ['112', '113', '114'])).
% 35.60/35.84  thf('116', plain,
% 35.60/35.84      (![X67 : $i, X68 : $i, X69 : $i]:
% 35.60/35.84         ((m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X68)))
% 35.60/35.84          | ~ (zip_tseitin_1 @ X67 @ X68 @ X69))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_8])).
% 35.60/35.84  thf('117', plain,
% 35.60/35.84      ((m1_subset_1 @ sk_D_1 @ 
% 35.60/35.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_C_1)))),
% 35.60/35.84      inference('sup-', [status(thm)], ['115', '116'])).
% 35.60/35.84  thf(cc3_relset_1, axiom,
% 35.60/35.84    (![A:$i,B:$i]:
% 35.60/35.84     ( ( v1_xboole_0 @ A ) =>
% 35.60/35.84       ( ![C:$i]:
% 35.60/35.84         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 35.60/35.84           ( v1_xboole_0 @ C ) ) ) ))).
% 35.60/35.84  thf('118', plain,
% 35.60/35.84      (![X42 : $i, X43 : $i, X44 : $i]:
% 35.60/35.84         (~ (v1_xboole_0 @ X42)
% 35.60/35.84          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X44)))
% 35.60/35.84          | (v1_xboole_0 @ X43))),
% 35.60/35.84      inference('cnf', [status(esa)], [cc3_relset_1])).
% 35.60/35.84  thf('119', plain,
% 35.60/35.84      (((v1_xboole_0 @ sk_D_1) | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_1)))),
% 35.60/35.84      inference('sup-', [status(thm)], ['117', '118'])).
% 35.60/35.84  thf('120', plain,
% 35.60/35.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C_1)))),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf(cc6_funct_2, axiom,
% 35.60/35.84    (![A:$i,B:$i]:
% 35.60/35.84     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 35.60/35.84       ( ![C:$i]:
% 35.60/35.84         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 35.60/35.84           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 35.60/35.84             ( ( v1_funct_1 @ C ) & ( ~( v1_xboole_0 @ C ) ) & 
% 35.60/35.84               ( v1_funct_2 @ C @ A @ B ) ) ) ) ) ))).
% 35.60/35.84  thf('121', plain,
% 35.60/35.84      (![X51 : $i, X52 : $i, X53 : $i]:
% 35.60/35.84         ((v1_xboole_0 @ X51)
% 35.60/35.84          | (v1_xboole_0 @ X52)
% 35.60/35.84          | ~ (v1_funct_1 @ X53)
% 35.60/35.84          | ~ (v1_funct_2 @ X53 @ X51 @ X52)
% 35.60/35.84          | ~ (v1_xboole_0 @ X53)
% 35.60/35.84          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52))))),
% 35.60/35.84      inference('cnf', [status(esa)], [cc6_funct_2])).
% 35.60/35.84  thf('122', plain,
% 35.60/35.84      ((~ (v1_xboole_0 @ sk_D_1)
% 35.60/35.84        | ~ (v1_funct_2 @ sk_D_1 @ sk_B_2 @ sk_C_1)
% 35.60/35.84        | ~ (v1_funct_1 @ sk_D_1)
% 35.60/35.84        | (v1_xboole_0 @ sk_C_1)
% 35.60/35.84        | (v1_xboole_0 @ sk_B_2))),
% 35.60/35.84      inference('sup-', [status(thm)], ['120', '121'])).
% 35.60/35.84  thf('123', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_2 @ sk_C_1)),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('124', plain, ((v1_funct_1 @ sk_D_1)),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('125', plain,
% 35.60/35.84      ((~ (v1_xboole_0 @ sk_D_1)
% 35.60/35.84        | (v1_xboole_0 @ sk_C_1)
% 35.60/35.84        | (v1_xboole_0 @ sk_B_2))),
% 35.60/35.84      inference('demod', [status(thm)], ['122', '123', '124'])).
% 35.60/35.84  thf('126', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 35.60/35.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.60/35.84  thf('127', plain, (((v1_xboole_0 @ sk_B_2) | ~ (v1_xboole_0 @ sk_D_1))),
% 35.60/35.84      inference('clc', [status(thm)], ['125', '126'])).
% 35.60/35.84  thf('128', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 35.60/35.84      inference('simplify_reflect+', [status(thm)], ['14', '15'])).
% 35.60/35.84  thf('129', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 35.60/35.84      inference('clc', [status(thm)], ['127', '128'])).
% 35.60/35.84  thf('130', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_1))),
% 35.60/35.84      inference('clc', [status(thm)], ['119', '129'])).
% 35.60/35.84  thf('131', plain,
% 35.60/35.84      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_C_1) = (k1_xboole_0)))),
% 35.60/35.84      inference('sup-', [status(thm)], ['90', '130'])).
% 35.60/35.84  thf('132', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 35.60/35.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 35.60/35.84  thf('133', plain, (((sk_C_1) = (k1_xboole_0))),
% 35.60/35.84      inference('demod', [status(thm)], ['131', '132'])).
% 35.60/35.84  thf('134', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 35.60/35.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 35.60/35.84  thf('135', plain, ($false),
% 35.60/35.84      inference('demod', [status(thm)], ['0', '133', '134'])).
% 35.60/35.84  
% 35.60/35.84  % SZS output end Refutation
% 35.60/35.84  
% 35.60/35.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

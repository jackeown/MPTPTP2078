%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oQ9IXfSH6T

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:03 EST 2020

% Result     : Theorem 1.03s
% Output     : Refutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 318 expanded)
%              Number of leaves         :   51 ( 117 expanded)
%              Depth                    :   23
%              Number of atoms          : 1506 (5955 expanded)
%              Number of equality atoms :   68 ( 238 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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

thf('10',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( zip_tseitin_1 @ X50 @ X51 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X51 @ X50 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) )
      | ( zip_tseitin_0 @ X52 @ X53 @ X51 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X51 @ X50 @ X52 ) @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ X0 )
      | ( zip_tseitin_0 @ sk_D @ X0 @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('14',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ( zip_tseitin_0 @ sk_D @ X0 @ sk_B_1 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','14','15','16'])).

thf('18',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
    | ( zip_tseitin_0 @ sk_D @ ( k2_relat_1 @ sk_D ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( v1_funct_2 @ X45 @ X47 @ X46 )
      | ~ ( zip_tseitin_0 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('20',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
    | ( v1_funct_2 @ sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
    | ( zip_tseitin_0 @ sk_D @ ( k2_relat_1 @ sk_D ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('22',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ~ ( zip_tseitin_0 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('24',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ X41 @ X42 )
      | ( X43 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X44 @ X41 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_D ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_D ) )
      | ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) )
      | ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','29'])).

thf('31',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('36',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['30','39'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('41',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X32 @ ( k1_relat_1 @ X33 ) )
      | ( ( k7_partfun1 @ X34 @ X33 @ X32 )
        = ( k1_funct_1 @ X33 @ X32 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v5_relat_1 @ X33 @ X34 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
      | ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('44',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('45',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
      | ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['42','45','46'])).

thf('48',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','47'])).

thf('49',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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

thf('53',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X38 @ X36 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X36 @ X37 @ X40 @ X35 @ X39 ) @ X38 )
        = ( k1_funct_1 @ X39 @ ( k1_funct_1 @ X35 @ X38 ) ) )
      | ( X36 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X36 @ X37 @ X35 ) @ ( k1_relset_1 @ X37 @ X40 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ( v1_xboole_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('56',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['51','60'])).

thf('62',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('64',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('66',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['61','66','67','68'])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['50','71'])).

thf('73',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['49','72'])).

thf('74',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','73'])).

thf('75',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('80',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['84'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('86',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('87',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('88',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['85','90'])).

thf('92',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['75','91'])).

thf('93',plain,(
    ! [X48: $i,X49: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('94',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('95',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('96',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['86','89'])).

thf('98',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('100',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['96','97','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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

thf('103',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ( v1_xboole_0 @ X30 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc6_funct_2])).

thf('104',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['85','90'])).

thf('111',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['101','111'])).

thf('113',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['86','89'])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['0','112','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oQ9IXfSH6T
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:26:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 1.03/1.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.03/1.21  % Solved by: fo/fo7.sh
% 1.03/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.03/1.21  % done 892 iterations in 0.752s
% 1.03/1.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.03/1.21  % SZS output start Refutation
% 1.03/1.21  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.03/1.21  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.03/1.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.03/1.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.03/1.21  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.03/1.21  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.03/1.21  thf(sk_F_type, type, sk_F: $i).
% 1.03/1.21  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.03/1.21  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.03/1.21  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.03/1.21  thf(sk_B_type, type, sk_B: $i > $i).
% 1.03/1.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.03/1.21  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.03/1.21  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.03/1.21  thf(sk_A_type, type, sk_A: $i).
% 1.03/1.21  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.03/1.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.03/1.21  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.03/1.21  thf(sk_D_type, type, sk_D: $i).
% 1.03/1.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.03/1.21  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 1.03/1.21  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.03/1.21  thf(sk_E_type, type, sk_E: $i).
% 1.03/1.21  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.03/1.21  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.03/1.21  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 1.03/1.21  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 1.03/1.21  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.03/1.21  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.03/1.21  thf(t186_funct_2, conjecture,
% 1.03/1.21    (![A:$i,B:$i,C:$i]:
% 1.03/1.21     ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.03/1.21       ( ![D:$i]:
% 1.03/1.21         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.03/1.21             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.03/1.21           ( ![E:$i]:
% 1.03/1.21             ( ( ( v1_funct_1 @ E ) & 
% 1.03/1.21                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 1.03/1.21               ( ![F:$i]:
% 1.03/1.21                 ( ( m1_subset_1 @ F @ B ) =>
% 1.03/1.21                   ( ( r1_tarski @
% 1.03/1.21                       ( k2_relset_1 @ B @ C @ D ) @ 
% 1.03/1.21                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 1.03/1.21                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.03/1.21                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 1.03/1.21                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.03/1.21  thf(zf_stmt_0, negated_conjecture,
% 1.03/1.21    (~( ![A:$i,B:$i,C:$i]:
% 1.03/1.21        ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.03/1.21          ( ![D:$i]:
% 1.03/1.21            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.03/1.21                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.03/1.21              ( ![E:$i]:
% 1.03/1.21                ( ( ( v1_funct_1 @ E ) & 
% 1.03/1.21                    ( m1_subset_1 @
% 1.03/1.21                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 1.03/1.21                  ( ![F:$i]:
% 1.03/1.21                    ( ( m1_subset_1 @ F @ B ) =>
% 1.03/1.21                      ( ( r1_tarski @
% 1.03/1.21                          ( k2_relset_1 @ B @ C @ D ) @ 
% 1.03/1.21                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 1.03/1.21                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.03/1.21                          ( ( k1_funct_1 @
% 1.03/1.21                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 1.03/1.21                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.03/1.21    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 1.03/1.21  thf('0', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('1', plain,
% 1.03/1.21      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf(cc2_relset_1, axiom,
% 1.03/1.21    (![A:$i,B:$i,C:$i]:
% 1.03/1.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.21       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.03/1.21  thf('2', plain,
% 1.03/1.21      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.03/1.21         ((v5_relat_1 @ X20 @ X22)
% 1.03/1.21          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.03/1.21      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.03/1.21  thf('3', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 1.03/1.21      inference('sup-', [status(thm)], ['1', '2'])).
% 1.03/1.21  thf('4', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf(t2_subset, axiom,
% 1.03/1.21    (![A:$i,B:$i]:
% 1.03/1.21     ( ( m1_subset_1 @ A @ B ) =>
% 1.03/1.21       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.03/1.21  thf('5', plain,
% 1.03/1.21      (![X11 : $i, X12 : $i]:
% 1.03/1.21         ((r2_hidden @ X11 @ X12)
% 1.03/1.21          | (v1_xboole_0 @ X12)
% 1.03/1.21          | ~ (m1_subset_1 @ X11 @ X12))),
% 1.03/1.21      inference('cnf', [status(esa)], [t2_subset])).
% 1.03/1.21  thf('6', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 1.03/1.21      inference('sup-', [status(thm)], ['4', '5'])).
% 1.03/1.21  thf(d10_xboole_0, axiom,
% 1.03/1.21    (![A:$i,B:$i]:
% 1.03/1.21     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.03/1.21  thf('7', plain,
% 1.03/1.21      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 1.03/1.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.03/1.21  thf('8', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 1.03/1.21      inference('simplify', [status(thm)], ['7'])).
% 1.03/1.21  thf('9', plain,
% 1.03/1.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf(t8_funct_2, axiom,
% 1.03/1.21    (![A:$i,B:$i,C:$i,D:$i]:
% 1.03/1.21     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.03/1.21         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.03/1.21       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 1.03/1.21         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 1.03/1.21             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 1.03/1.21           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.03/1.21  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.03/1.21  thf(zf_stmt_2, axiom,
% 1.03/1.21    (![B:$i,A:$i]:
% 1.03/1.21     ( ( zip_tseitin_1 @ B @ A ) =>
% 1.03/1.21       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 1.03/1.21  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 1.03/1.21  thf(zf_stmt_4, axiom,
% 1.03/1.21    (![D:$i,C:$i,A:$i]:
% 1.03/1.21     ( ( zip_tseitin_0 @ D @ C @ A ) =>
% 1.03/1.22       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.03/1.22         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 1.03/1.22  thf(zf_stmt_5, axiom,
% 1.03/1.22    (![A:$i,B:$i,C:$i,D:$i]:
% 1.03/1.22     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.03/1.22         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.03/1.22       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 1.03/1.22         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ A ) ) ) ))).
% 1.03/1.22  thf('10', plain,
% 1.03/1.22      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 1.03/1.22         ((zip_tseitin_1 @ X50 @ X51)
% 1.03/1.22          | ~ (v1_funct_1 @ X52)
% 1.03/1.22          | ~ (v1_funct_2 @ X52 @ X51 @ X50)
% 1.03/1.22          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))
% 1.03/1.22          | (zip_tseitin_0 @ X52 @ X53 @ X51)
% 1.03/1.22          | ~ (r1_tarski @ (k2_relset_1 @ X51 @ X50 @ X52) @ X53))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.03/1.22  thf('11', plain,
% 1.03/1.22      (![X0 : $i]:
% 1.03/1.22         (~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ X0)
% 1.03/1.22          | (zip_tseitin_0 @ sk_D @ X0 @ sk_B_1)
% 1.03/1.22          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 1.03/1.22          | ~ (v1_funct_1 @ sk_D)
% 1.03/1.22          | (zip_tseitin_1 @ sk_C_1 @ sk_B_1))),
% 1.03/1.22      inference('sup-', [status(thm)], ['9', '10'])).
% 1.03/1.22  thf('12', plain,
% 1.03/1.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf(redefinition_k2_relset_1, axiom,
% 1.03/1.22    (![A:$i,B:$i,C:$i]:
% 1.03/1.22     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.22       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.03/1.22  thf('13', plain,
% 1.03/1.22      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.03/1.22         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 1.03/1.22          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.03/1.22      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.03/1.22  thf('14', plain,
% 1.03/1.22      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.03/1.22      inference('sup-', [status(thm)], ['12', '13'])).
% 1.03/1.22  thf('15', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('17', plain,
% 1.03/1.22      (![X0 : $i]:
% 1.03/1.22         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0)
% 1.03/1.22          | (zip_tseitin_0 @ sk_D @ X0 @ sk_B_1)
% 1.03/1.22          | (zip_tseitin_1 @ sk_C_1 @ sk_B_1))),
% 1.03/1.22      inference('demod', [status(thm)], ['11', '14', '15', '16'])).
% 1.03/1.22  thf('18', plain,
% 1.03/1.22      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 1.03/1.22        | (zip_tseitin_0 @ sk_D @ (k2_relat_1 @ sk_D) @ sk_B_1))),
% 1.03/1.22      inference('sup-', [status(thm)], ['8', '17'])).
% 1.03/1.22  thf('19', plain,
% 1.03/1.22      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.03/1.22         ((v1_funct_2 @ X45 @ X47 @ X46) | ~ (zip_tseitin_0 @ X45 @ X46 @ X47))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.03/1.22  thf('20', plain,
% 1.03/1.22      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 1.03/1.22        | (v1_funct_2 @ sk_D @ sk_B_1 @ (k2_relat_1 @ sk_D)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['18', '19'])).
% 1.03/1.22  thf('21', plain,
% 1.03/1.22      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 1.03/1.22        | (zip_tseitin_0 @ sk_D @ (k2_relat_1 @ sk_D) @ sk_B_1))),
% 1.03/1.22      inference('sup-', [status(thm)], ['8', '17'])).
% 1.03/1.22  thf('22', plain,
% 1.03/1.22      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.03/1.22         ((m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 1.03/1.22          | ~ (zip_tseitin_0 @ X45 @ X46 @ X47))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.03/1.22  thf('23', plain,
% 1.03/1.22      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 1.03/1.22        | (m1_subset_1 @ sk_D @ 
% 1.03/1.22           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ sk_D)))))),
% 1.03/1.22      inference('sup-', [status(thm)], ['21', '22'])).
% 1.03/1.22  thf(t7_funct_2, axiom,
% 1.03/1.22    (![A:$i,B:$i,C:$i,D:$i]:
% 1.03/1.22     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.03/1.22         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.03/1.22       ( ( r2_hidden @ C @ A ) =>
% 1.03/1.22         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.03/1.22           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 1.03/1.22  thf('24', plain,
% 1.03/1.22      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.03/1.22         (~ (r2_hidden @ X41 @ X42)
% 1.03/1.22          | ((X43) = (k1_xboole_0))
% 1.03/1.22          | ~ (v1_funct_1 @ X44)
% 1.03/1.22          | ~ (v1_funct_2 @ X44 @ X42 @ X43)
% 1.03/1.22          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 1.03/1.22          | (r2_hidden @ (k1_funct_1 @ X44 @ X41) @ X43))),
% 1.03/1.22      inference('cnf', [status(esa)], [t7_funct_2])).
% 1.03/1.22  thf('25', plain,
% 1.03/1.22      (![X0 : $i]:
% 1.03/1.22         ((zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 1.03/1.22          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))
% 1.03/1.22          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ (k2_relat_1 @ sk_D))
% 1.03/1.22          | ~ (v1_funct_1 @ sk_D)
% 1.03/1.22          | ((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 1.03/1.22          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.03/1.22      inference('sup-', [status(thm)], ['23', '24'])).
% 1.03/1.22  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('27', plain,
% 1.03/1.22      (![X0 : $i]:
% 1.03/1.22         ((zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 1.03/1.22          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))
% 1.03/1.22          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ (k2_relat_1 @ sk_D))
% 1.03/1.22          | ((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 1.03/1.22          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.03/1.22      inference('demod', [status(thm)], ['25', '26'])).
% 1.03/1.22  thf('28', plain,
% 1.03/1.22      (![X0 : $i]:
% 1.03/1.22         ((zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 1.03/1.22          | ~ (r2_hidden @ X0 @ sk_B_1)
% 1.03/1.22          | ((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 1.03/1.22          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))
% 1.03/1.22          | (zip_tseitin_1 @ sk_C_1 @ sk_B_1))),
% 1.03/1.22      inference('sup-', [status(thm)], ['20', '27'])).
% 1.03/1.22  thf('29', plain,
% 1.03/1.22      (![X0 : $i]:
% 1.03/1.22         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))
% 1.03/1.22          | ((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 1.03/1.22          | ~ (r2_hidden @ X0 @ sk_B_1)
% 1.03/1.22          | (zip_tseitin_1 @ sk_C_1 @ sk_B_1))),
% 1.03/1.22      inference('simplify', [status(thm)], ['28'])).
% 1.03/1.22  thf('30', plain,
% 1.03/1.22      (((v1_xboole_0 @ sk_B_1)
% 1.03/1.22        | (zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 1.03/1.22        | ((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 1.03/1.22        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k2_relat_1 @ sk_D)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['6', '29'])).
% 1.03/1.22  thf('31', plain,
% 1.03/1.22      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 1.03/1.22        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf(d3_tarski, axiom,
% 1.03/1.22    (![A:$i,B:$i]:
% 1.03/1.22     ( ( r1_tarski @ A @ B ) <=>
% 1.03/1.22       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.03/1.22  thf('32', plain,
% 1.03/1.22      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.03/1.22         (~ (r2_hidden @ X3 @ X4)
% 1.03/1.22          | (r2_hidden @ X3 @ X5)
% 1.03/1.22          | ~ (r1_tarski @ X4 @ X5))),
% 1.03/1.22      inference('cnf', [status(esa)], [d3_tarski])).
% 1.03/1.22  thf('33', plain,
% 1.03/1.22      (![X0 : $i]:
% 1.03/1.22         ((r2_hidden @ X0 @ (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))
% 1.03/1.22          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['31', '32'])).
% 1.03/1.22  thf('34', plain,
% 1.03/1.22      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf(redefinition_k1_relset_1, axiom,
% 1.03/1.22    (![A:$i,B:$i,C:$i]:
% 1.03/1.22     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.22       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.03/1.22  thf('35', plain,
% 1.03/1.22      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.03/1.22         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 1.03/1.22          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.03/1.22      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.03/1.22  thf('36', plain,
% 1.03/1.22      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.03/1.22      inference('sup-', [status(thm)], ['34', '35'])).
% 1.03/1.22  thf('37', plain,
% 1.03/1.22      (![X0 : $i]:
% 1.03/1.22         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 1.03/1.22          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 1.03/1.22      inference('demod', [status(thm)], ['33', '36'])).
% 1.03/1.22  thf('38', plain,
% 1.03/1.22      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.03/1.22      inference('sup-', [status(thm)], ['12', '13'])).
% 1.03/1.22  thf('39', plain,
% 1.03/1.22      (![X0 : $i]:
% 1.03/1.22         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 1.03/1.22          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 1.03/1.22      inference('demod', [status(thm)], ['37', '38'])).
% 1.03/1.22  thf('40', plain,
% 1.03/1.22      ((((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 1.03/1.22        | (zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 1.03/1.22        | (v1_xboole_0 @ sk_B_1)
% 1.03/1.22        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['30', '39'])).
% 1.03/1.22  thf(d8_partfun1, axiom,
% 1.03/1.22    (![A:$i,B:$i]:
% 1.03/1.22     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 1.03/1.22       ( ![C:$i]:
% 1.03/1.22         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 1.03/1.22           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 1.03/1.22  thf('41', plain,
% 1.03/1.22      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.03/1.22         (~ (r2_hidden @ X32 @ (k1_relat_1 @ X33))
% 1.03/1.22          | ((k7_partfun1 @ X34 @ X33 @ X32) = (k1_funct_1 @ X33 @ X32))
% 1.03/1.22          | ~ (v1_funct_1 @ X33)
% 1.03/1.22          | ~ (v5_relat_1 @ X33 @ X34)
% 1.03/1.22          | ~ (v1_relat_1 @ X33))),
% 1.03/1.22      inference('cnf', [status(esa)], [d8_partfun1])).
% 1.03/1.22  thf('42', plain,
% 1.03/1.22      (![X0 : $i]:
% 1.03/1.22         ((v1_xboole_0 @ sk_B_1)
% 1.03/1.22          | (zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 1.03/1.22          | ((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 1.03/1.22          | ~ (v1_relat_1 @ sk_E)
% 1.03/1.22          | ~ (v5_relat_1 @ sk_E @ X0)
% 1.03/1.22          | ~ (v1_funct_1 @ sk_E)
% 1.03/1.22          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 1.03/1.22              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 1.03/1.22      inference('sup-', [status(thm)], ['40', '41'])).
% 1.03/1.22  thf('43', plain,
% 1.03/1.22      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf(cc1_relset_1, axiom,
% 1.03/1.22    (![A:$i,B:$i,C:$i]:
% 1.03/1.22     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.22       ( v1_relat_1 @ C ) ))).
% 1.03/1.22  thf('44', plain,
% 1.03/1.22      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.03/1.22         ((v1_relat_1 @ X17)
% 1.03/1.22          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.03/1.22      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.03/1.22  thf('45', plain, ((v1_relat_1 @ sk_E)),
% 1.03/1.22      inference('sup-', [status(thm)], ['43', '44'])).
% 1.03/1.22  thf('46', plain, ((v1_funct_1 @ sk_E)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('47', plain,
% 1.03/1.22      (![X0 : $i]:
% 1.03/1.22         ((v1_xboole_0 @ sk_B_1)
% 1.03/1.22          | (zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 1.03/1.22          | ((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 1.03/1.22          | ~ (v5_relat_1 @ sk_E @ X0)
% 1.03/1.22          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 1.03/1.22              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 1.03/1.22      inference('demod', [status(thm)], ['42', '45', '46'])).
% 1.03/1.22  thf('48', plain,
% 1.03/1.22      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 1.03/1.22          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 1.03/1.22        | ((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 1.03/1.22        | (zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 1.03/1.22        | (v1_xboole_0 @ sk_B_1))),
% 1.03/1.22      inference('sup-', [status(thm)], ['3', '47'])).
% 1.03/1.22  thf('49', plain,
% 1.03/1.22      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 1.03/1.22         sk_F) != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('50', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('51', plain,
% 1.03/1.22      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.03/1.22      inference('sup-', [status(thm)], ['34', '35'])).
% 1.03/1.22  thf('52', plain,
% 1.03/1.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf(t185_funct_2, axiom,
% 1.03/1.22    (![A:$i,B:$i,C:$i]:
% 1.03/1.22     ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.03/1.22       ( ![D:$i]:
% 1.03/1.22         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.03/1.22             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.03/1.22           ( ![E:$i]:
% 1.03/1.22             ( ( ( v1_funct_1 @ E ) & 
% 1.03/1.22                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 1.03/1.22               ( ![F:$i]:
% 1.03/1.22                 ( ( m1_subset_1 @ F @ B ) =>
% 1.03/1.22                   ( ( r1_tarski @
% 1.03/1.22                       ( k2_relset_1 @ B @ C @ D ) @ 
% 1.03/1.22                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 1.03/1.22                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.03/1.22                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 1.03/1.22                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.03/1.22  thf('53', plain,
% 1.03/1.22      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.03/1.22         (~ (v1_funct_1 @ X35)
% 1.03/1.22          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 1.03/1.22          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.03/1.22          | ~ (m1_subset_1 @ X38 @ X36)
% 1.03/1.22          | ((k1_funct_1 @ (k8_funct_2 @ X36 @ X37 @ X40 @ X35 @ X39) @ X38)
% 1.03/1.22              = (k1_funct_1 @ X39 @ (k1_funct_1 @ X35 @ X38)))
% 1.03/1.22          | ((X36) = (k1_xboole_0))
% 1.03/1.22          | ~ (r1_tarski @ (k2_relset_1 @ X36 @ X37 @ X35) @ 
% 1.03/1.22               (k1_relset_1 @ X37 @ X40 @ X39))
% 1.03/1.22          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X40)))
% 1.03/1.22          | ~ (v1_funct_1 @ X39)
% 1.03/1.22          | (v1_xboole_0 @ X37))),
% 1.03/1.22      inference('cnf', [status(esa)], [t185_funct_2])).
% 1.03/1.22  thf('54', plain,
% 1.03/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.22         ((v1_xboole_0 @ sk_C_1)
% 1.03/1.22          | ~ (v1_funct_1 @ X0)
% 1.03/1.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 1.03/1.22          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 1.03/1.22               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 1.03/1.22          | ((sk_B_1) = (k1_xboole_0))
% 1.03/1.22          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 1.03/1.22              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 1.03/1.22          | ~ (m1_subset_1 @ X2 @ sk_B_1)
% 1.03/1.22          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 1.03/1.22          | ~ (v1_funct_1 @ sk_D))),
% 1.03/1.22      inference('sup-', [status(thm)], ['52', '53'])).
% 1.03/1.22  thf('55', plain,
% 1.03/1.22      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.03/1.22      inference('sup-', [status(thm)], ['12', '13'])).
% 1.03/1.22  thf('56', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('58', plain,
% 1.03/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.22         ((v1_xboole_0 @ sk_C_1)
% 1.03/1.22          | ~ (v1_funct_1 @ X0)
% 1.03/1.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 1.03/1.22          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 1.03/1.22               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 1.03/1.22          | ((sk_B_1) = (k1_xboole_0))
% 1.03/1.22          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 1.03/1.22              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 1.03/1.22          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 1.03/1.22      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 1.03/1.22  thf('59', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('60', plain,
% 1.03/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.22         ((v1_xboole_0 @ sk_C_1)
% 1.03/1.22          | ~ (v1_funct_1 @ X0)
% 1.03/1.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 1.03/1.22          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 1.03/1.22               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 1.03/1.22          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 1.03/1.22              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 1.03/1.22          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 1.03/1.22      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 1.03/1.22  thf('61', plain,
% 1.03/1.22      (![X0 : $i]:
% 1.03/1.22         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))
% 1.03/1.22          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 1.03/1.22          | ((k1_funct_1 @ 
% 1.03/1.22              (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 1.03/1.22              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 1.03/1.22          | ~ (m1_subset_1 @ sk_E @ 
% 1.03/1.22               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 1.03/1.22          | ~ (v1_funct_1 @ sk_E)
% 1.03/1.22          | (v1_xboole_0 @ sk_C_1))),
% 1.03/1.22      inference('sup-', [status(thm)], ['51', '60'])).
% 1.03/1.22  thf('62', plain,
% 1.03/1.22      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 1.03/1.22        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('63', plain,
% 1.03/1.22      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.03/1.22      inference('sup-', [status(thm)], ['34', '35'])).
% 1.03/1.22  thf('64', plain,
% 1.03/1.22      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 1.03/1.22        (k1_relat_1 @ sk_E))),
% 1.03/1.22      inference('demod', [status(thm)], ['62', '63'])).
% 1.03/1.22  thf('65', plain,
% 1.03/1.22      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.03/1.22      inference('sup-', [status(thm)], ['12', '13'])).
% 1.03/1.22  thf('66', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 1.03/1.22      inference('demod', [status(thm)], ['64', '65'])).
% 1.03/1.22  thf('67', plain,
% 1.03/1.22      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('69', plain,
% 1.03/1.22      (![X0 : $i]:
% 1.03/1.22         (~ (m1_subset_1 @ X0 @ sk_B_1)
% 1.03/1.22          | ((k1_funct_1 @ 
% 1.03/1.22              (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 1.03/1.22              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 1.03/1.22          | (v1_xboole_0 @ sk_C_1))),
% 1.03/1.22      inference('demod', [status(thm)], ['61', '66', '67', '68'])).
% 1.03/1.22  thf('70', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('71', plain,
% 1.03/1.22      (![X0 : $i]:
% 1.03/1.22         (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 1.03/1.22            X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 1.03/1.22          | ~ (m1_subset_1 @ X0 @ sk_B_1))),
% 1.03/1.22      inference('clc', [status(thm)], ['69', '70'])).
% 1.03/1.22  thf('72', plain,
% 1.03/1.22      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 1.03/1.22         sk_F) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['50', '71'])).
% 1.03/1.22  thf('73', plain,
% 1.03/1.22      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 1.03/1.22         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 1.03/1.22      inference('demod', [status(thm)], ['49', '72'])).
% 1.03/1.22  thf('74', plain,
% 1.03/1.22      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 1.03/1.22          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 1.03/1.22        | (v1_xboole_0 @ sk_B_1)
% 1.03/1.22        | (zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 1.03/1.22        | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['48', '73'])).
% 1.03/1.22  thf('75', plain,
% 1.03/1.22      ((((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 1.03/1.22        | (zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 1.03/1.22        | (v1_xboole_0 @ sk_B_1))),
% 1.03/1.22      inference('simplify', [status(thm)], ['74'])).
% 1.03/1.22  thf('76', plain,
% 1.03/1.22      (![X4 : $i, X6 : $i]:
% 1.03/1.22         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.03/1.22      inference('cnf', [status(esa)], [d3_tarski])).
% 1.03/1.22  thf(d1_xboole_0, axiom,
% 1.03/1.22    (![A:$i]:
% 1.03/1.22     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.03/1.22  thf('77', plain,
% 1.03/1.22      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.03/1.22      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.03/1.22  thf('78', plain,
% 1.03/1.22      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.03/1.22      inference('sup-', [status(thm)], ['76', '77'])).
% 1.03/1.22  thf('79', plain,
% 1.03/1.22      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.03/1.22      inference('sup-', [status(thm)], ['76', '77'])).
% 1.03/1.22  thf('80', plain,
% 1.03/1.22      (![X7 : $i, X9 : $i]:
% 1.03/1.22         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 1.03/1.22      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.03/1.22  thf('81', plain,
% 1.03/1.22      (![X0 : $i, X1 : $i]:
% 1.03/1.22         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['79', '80'])).
% 1.03/1.22  thf('82', plain,
% 1.03/1.22      (![X0 : $i, X1 : $i]:
% 1.03/1.22         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.03/1.22      inference('sup-', [status(thm)], ['78', '81'])).
% 1.03/1.22  thf('83', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('84', plain,
% 1.03/1.22      (![X0 : $i]:
% 1.03/1.22         (((X0) != (k1_xboole_0))
% 1.03/1.22          | ~ (v1_xboole_0 @ sk_B_1)
% 1.03/1.22          | ~ (v1_xboole_0 @ X0))),
% 1.03/1.22      inference('sup-', [status(thm)], ['82', '83'])).
% 1.03/1.22  thf('85', plain,
% 1.03/1.22      ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B_1))),
% 1.03/1.22      inference('simplify', [status(thm)], ['84'])).
% 1.03/1.22  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.03/1.22  thf('86', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 1.03/1.22      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.03/1.22  thf('87', plain,
% 1.03/1.22      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.03/1.22      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.03/1.22  thf(t7_ordinal1, axiom,
% 1.03/1.22    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.03/1.22  thf('88', plain,
% 1.03/1.22      (![X15 : $i, X16 : $i]:
% 1.03/1.22         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 1.03/1.22      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.03/1.22  thf('89', plain,
% 1.03/1.22      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['87', '88'])).
% 1.03/1.22  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.03/1.22      inference('sup-', [status(thm)], ['86', '89'])).
% 1.03/1.22  thf('91', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.03/1.22      inference('simplify_reflect+', [status(thm)], ['85', '90'])).
% 1.03/1.22  thf('92', plain,
% 1.03/1.22      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1)
% 1.03/1.22        | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 1.03/1.22      inference('clc', [status(thm)], ['75', '91'])).
% 1.03/1.22  thf('93', plain,
% 1.03/1.22      (![X48 : $i, X49 : $i]:
% 1.03/1.22         (((X48) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X48 @ X49))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.03/1.22  thf('94', plain,
% 1.03/1.22      ((((k2_relat_1 @ sk_D) = (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 1.03/1.22      inference('sup-', [status(thm)], ['92', '93'])).
% 1.03/1.22  thf(fc9_relat_1, axiom,
% 1.03/1.22    (![A:$i]:
% 1.03/1.22     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 1.03/1.22       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 1.03/1.22  thf('95', plain,
% 1.03/1.22      (![X13 : $i]:
% 1.03/1.22         (~ (v1_xboole_0 @ (k2_relat_1 @ X13))
% 1.03/1.22          | ~ (v1_relat_1 @ X13)
% 1.03/1.22          | (v1_xboole_0 @ X13))),
% 1.03/1.22      inference('cnf', [status(esa)], [fc9_relat_1])).
% 1.03/1.22  thf('96', plain,
% 1.03/1.22      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.03/1.22        | ((sk_C_1) = (k1_xboole_0))
% 1.03/1.22        | (v1_xboole_0 @ sk_D)
% 1.03/1.22        | ~ (v1_relat_1 @ sk_D))),
% 1.03/1.22      inference('sup-', [status(thm)], ['94', '95'])).
% 1.03/1.22  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.03/1.22      inference('sup-', [status(thm)], ['86', '89'])).
% 1.03/1.22  thf('98', plain,
% 1.03/1.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('99', plain,
% 1.03/1.22      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.03/1.22         ((v1_relat_1 @ X17)
% 1.03/1.22          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.03/1.22      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.03/1.22  thf('100', plain, ((v1_relat_1 @ sk_D)),
% 1.03/1.22      inference('sup-', [status(thm)], ['98', '99'])).
% 1.03/1.22  thf('101', plain, ((((sk_C_1) = (k1_xboole_0)) | (v1_xboole_0 @ sk_D))),
% 1.03/1.22      inference('demod', [status(thm)], ['96', '97', '100'])).
% 1.03/1.22  thf('102', plain,
% 1.03/1.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf(cc6_funct_2, axiom,
% 1.03/1.22    (![A:$i,B:$i]:
% 1.03/1.22     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 1.03/1.22       ( ![C:$i]:
% 1.03/1.22         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.22           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.03/1.22             ( ( v1_funct_1 @ C ) & ( ~( v1_xboole_0 @ C ) ) & 
% 1.03/1.22               ( v1_funct_2 @ C @ A @ B ) ) ) ) ) ))).
% 1.03/1.22  thf('103', plain,
% 1.03/1.22      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.03/1.22         ((v1_xboole_0 @ X29)
% 1.03/1.22          | (v1_xboole_0 @ X30)
% 1.03/1.22          | ~ (v1_funct_1 @ X31)
% 1.03/1.22          | ~ (v1_funct_2 @ X31 @ X29 @ X30)
% 1.03/1.22          | ~ (v1_xboole_0 @ X31)
% 1.03/1.22          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.03/1.22      inference('cnf', [status(esa)], [cc6_funct_2])).
% 1.03/1.22  thf('104', plain,
% 1.03/1.22      ((~ (v1_xboole_0 @ sk_D)
% 1.03/1.22        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 1.03/1.22        | ~ (v1_funct_1 @ sk_D)
% 1.03/1.22        | (v1_xboole_0 @ sk_C_1)
% 1.03/1.22        | (v1_xboole_0 @ sk_B_1))),
% 1.03/1.22      inference('sup-', [status(thm)], ['102', '103'])).
% 1.03/1.22  thf('105', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('106', plain, ((v1_funct_1 @ sk_D)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('107', plain,
% 1.03/1.22      ((~ (v1_xboole_0 @ sk_D)
% 1.03/1.22        | (v1_xboole_0 @ sk_C_1)
% 1.03/1.22        | (v1_xboole_0 @ sk_B_1))),
% 1.03/1.22      inference('demod', [status(thm)], ['104', '105', '106'])).
% 1.03/1.22  thf('108', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf('109', plain, (((v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ sk_D))),
% 1.03/1.22      inference('clc', [status(thm)], ['107', '108'])).
% 1.03/1.22  thf('110', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.03/1.22      inference('simplify_reflect+', [status(thm)], ['85', '90'])).
% 1.03/1.22  thf('111', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.03/1.22      inference('clc', [status(thm)], ['109', '110'])).
% 1.03/1.22  thf('112', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.03/1.22      inference('clc', [status(thm)], ['101', '111'])).
% 1.03/1.22  thf('113', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.03/1.22      inference('sup-', [status(thm)], ['86', '89'])).
% 1.03/1.22  thf('114', plain, ($false),
% 1.03/1.22      inference('demod', [status(thm)], ['0', '112', '113'])).
% 1.03/1.22  
% 1.03/1.22  % SZS output end Refutation
% 1.03/1.22  
% 1.03/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

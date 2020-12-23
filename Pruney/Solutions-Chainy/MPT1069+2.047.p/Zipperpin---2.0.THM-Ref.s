%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c10kSnt1jS

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:07 EST 2020

% Result     : Theorem 22.92s
% Output     : Refutation 22.92s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 227 expanded)
%              Number of leaves         :   51 (  89 expanded)
%              Depth                    :   17
%              Number of atoms          : 1254 (4477 expanded)
%              Number of equality atoms :   65 ( 192 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('3',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( m1_subset_1 @ X49 @ X47 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X47 @ X48 @ X51 @ X46 @ X50 ) @ X49 )
        = ( k1_funct_1 @ X50 @ ( k1_funct_1 @ X46 @ X49 ) ) )
      | ( X47 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X47 @ X48 @ X46 ) @ ( k1_relset_1 @ X48 @ X51 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X51 ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ( v1_xboole_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('6',plain,(
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
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X34 @ X32 )
        = ( k2_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['6','9','10','11'])).

thf('13',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('18',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('20',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['15','20','21','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('29',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X26 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('30',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_C_1 @ sk_A @ sk_E ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_C_1 @ sk_A @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X34 @ X32 )
        = ( k2_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('35',plain,
    ( ( k2_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k2_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_A ),
    inference(demod,[status(thm)],['32','35'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('37',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( v5_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( v5_relat_1 @ sk_E @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('40',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('41',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( m1_subset_1 @ ( k1_tarski @ X15 ) @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_F ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_F ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    r1_tarski @ ( k1_tarski @ sk_F ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['47','48'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('50',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k1_tarski @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('51',plain,(
    r2_hidden @ sk_F @ sk_B_1 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
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

thf('53',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('54',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('57',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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

thf('60',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('61',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('63',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('64',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ X10 )
        = X10 )
      | ~ ( r2_hidden @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('66',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ X13 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','68'])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C_1 @ X0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['61','71'])).

thf('73',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['58','72'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('74',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X22 @ X21 ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('78',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['75','78','79'])).

thf('81',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['51','80'])).

thf('82',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('83',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('88',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X43 @ ( k1_relat_1 @ X44 ) )
      | ( ( k7_partfun1 @ X45 @ X44 @ X43 )
        = ( k1_funct_1 @ X44 @ X43 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v5_relat_1 @ X44 @ X45 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['39','40'])).

thf('91',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['42','92'])).

thf('94',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['27','93'])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c10kSnt1jS
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:23:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 22.92/23.16  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 22.92/23.16  % Solved by: fo/fo7.sh
% 22.92/23.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 22.92/23.16  % done 8588 iterations in 22.702s
% 22.92/23.16  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 22.92/23.16  % SZS output start Refutation
% 22.92/23.16  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 22.92/23.16  thf(sk_B_1_type, type, sk_B_1: $i).
% 22.92/23.16  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 22.92/23.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 22.92/23.16  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 22.92/23.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 22.92/23.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 22.92/23.16  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 22.92/23.16  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 22.92/23.16  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 22.92/23.16  thf(sk_E_type, type, sk_E: $i).
% 22.92/23.16  thf(sk_D_type, type, sk_D: $i).
% 22.92/23.16  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 22.92/23.16  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 22.92/23.16  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 22.92/23.16  thf(sk_C_1_type, type, sk_C_1: $i).
% 22.92/23.16  thf(sk_A_type, type, sk_A: $i).
% 22.92/23.16  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 22.92/23.16  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 22.92/23.16  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 22.92/23.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 22.92/23.16  thf(sk_F_type, type, sk_F: $i).
% 22.92/23.16  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 22.92/23.16  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 22.92/23.16  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 22.92/23.16  thf(sk_B_type, type, sk_B: $i > $i).
% 22.92/23.16  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 22.92/23.16  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 22.92/23.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 22.92/23.16  thf(t186_funct_2, conjecture,
% 22.92/23.16    (![A:$i,B:$i,C:$i]:
% 22.92/23.16     ( ( ~( v1_xboole_0 @ C ) ) =>
% 22.92/23.16       ( ![D:$i]:
% 22.92/23.16         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 22.92/23.16             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 22.92/23.16           ( ![E:$i]:
% 22.92/23.16             ( ( ( v1_funct_1 @ E ) & 
% 22.92/23.16                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 22.92/23.16               ( ![F:$i]:
% 22.92/23.16                 ( ( m1_subset_1 @ F @ B ) =>
% 22.92/23.16                   ( ( r1_tarski @
% 22.92/23.16                       ( k2_relset_1 @ B @ C @ D ) @ 
% 22.92/23.16                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 22.92/23.16                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 22.92/23.16                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 22.92/23.16                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 22.92/23.16  thf(zf_stmt_0, negated_conjecture,
% 22.92/23.16    (~( ![A:$i,B:$i,C:$i]:
% 22.92/23.16        ( ( ~( v1_xboole_0 @ C ) ) =>
% 22.92/23.16          ( ![D:$i]:
% 22.92/23.16            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 22.92/23.16                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 22.92/23.16              ( ![E:$i]:
% 22.92/23.16                ( ( ( v1_funct_1 @ E ) & 
% 22.92/23.16                    ( m1_subset_1 @
% 22.92/23.16                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 22.92/23.16                  ( ![F:$i]:
% 22.92/23.16                    ( ( m1_subset_1 @ F @ B ) =>
% 22.92/23.16                      ( ( r1_tarski @
% 22.92/23.16                          ( k2_relset_1 @ B @ C @ D ) @ 
% 22.92/23.16                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 22.92/23.16                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 22.92/23.16                          ( ( k1_funct_1 @
% 22.92/23.16                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 22.92/23.16                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 22.92/23.16    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 22.92/23.16  thf('0', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf('1', plain,
% 22.92/23.16      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf(redefinition_k1_relset_1, axiom,
% 22.92/23.16    (![A:$i,B:$i,C:$i]:
% 22.92/23.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 22.92/23.16       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 22.92/23.16  thf('2', plain,
% 22.92/23.16      (![X29 : $i, X30 : $i, X31 : $i]:
% 22.92/23.16         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 22.92/23.16          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 22.92/23.16      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 22.92/23.16  thf('3', plain,
% 22.92/23.16      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 22.92/23.16      inference('sup-', [status(thm)], ['1', '2'])).
% 22.92/23.16  thf('4', plain,
% 22.92/23.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf(t185_funct_2, axiom,
% 22.92/23.16    (![A:$i,B:$i,C:$i]:
% 22.92/23.16     ( ( ~( v1_xboole_0 @ C ) ) =>
% 22.92/23.16       ( ![D:$i]:
% 22.92/23.16         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 22.92/23.16             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 22.92/23.16           ( ![E:$i]:
% 22.92/23.16             ( ( ( v1_funct_1 @ E ) & 
% 22.92/23.16                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 22.92/23.16               ( ![F:$i]:
% 22.92/23.16                 ( ( m1_subset_1 @ F @ B ) =>
% 22.92/23.16                   ( ( r1_tarski @
% 22.92/23.16                       ( k2_relset_1 @ B @ C @ D ) @ 
% 22.92/23.16                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 22.92/23.16                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 22.92/23.16                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 22.92/23.16                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 22.92/23.16  thf('5', plain,
% 22.92/23.16      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 22.92/23.16         (~ (v1_funct_1 @ X46)
% 22.92/23.16          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 22.92/23.16          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 22.92/23.16          | ~ (m1_subset_1 @ X49 @ X47)
% 22.92/23.16          | ((k1_funct_1 @ (k8_funct_2 @ X47 @ X48 @ X51 @ X46 @ X50) @ X49)
% 22.92/23.16              = (k1_funct_1 @ X50 @ (k1_funct_1 @ X46 @ X49)))
% 22.92/23.16          | ((X47) = (k1_xboole_0))
% 22.92/23.16          | ~ (r1_tarski @ (k2_relset_1 @ X47 @ X48 @ X46) @ 
% 22.92/23.16               (k1_relset_1 @ X48 @ X51 @ X50))
% 22.92/23.16          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X51)))
% 22.92/23.16          | ~ (v1_funct_1 @ X50)
% 22.92/23.16          | (v1_xboole_0 @ X48))),
% 22.92/23.16      inference('cnf', [status(esa)], [t185_funct_2])).
% 22.92/23.16  thf('6', plain,
% 22.92/23.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.92/23.16         ((v1_xboole_0 @ sk_C_1)
% 22.92/23.16          | ~ (v1_funct_1 @ X0)
% 22.92/23.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 22.92/23.16          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 22.92/23.16               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 22.92/23.16          | ((sk_B_1) = (k1_xboole_0))
% 22.92/23.16          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 22.92/23.16              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 22.92/23.16          | ~ (m1_subset_1 @ X2 @ sk_B_1)
% 22.92/23.16          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 22.92/23.16          | ~ (v1_funct_1 @ sk_D))),
% 22.92/23.16      inference('sup-', [status(thm)], ['4', '5'])).
% 22.92/23.16  thf('7', plain,
% 22.92/23.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf(redefinition_k2_relset_1, axiom,
% 22.92/23.16    (![A:$i,B:$i,C:$i]:
% 22.92/23.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 22.92/23.16       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 22.92/23.16  thf('8', plain,
% 22.92/23.16      (![X32 : $i, X33 : $i, X34 : $i]:
% 22.92/23.16         (((k2_relset_1 @ X33 @ X34 @ X32) = (k2_relat_1 @ X32))
% 22.92/23.16          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 22.92/23.16      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 22.92/23.16  thf('9', plain,
% 22.92/23.16      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 22.92/23.16      inference('sup-', [status(thm)], ['7', '8'])).
% 22.92/23.16  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf('12', plain,
% 22.92/23.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.92/23.16         ((v1_xboole_0 @ sk_C_1)
% 22.92/23.16          | ~ (v1_funct_1 @ X0)
% 22.92/23.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 22.92/23.16          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 22.92/23.16               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 22.92/23.16          | ((sk_B_1) = (k1_xboole_0))
% 22.92/23.16          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 22.92/23.16              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 22.92/23.16          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 22.92/23.16      inference('demod', [status(thm)], ['6', '9', '10', '11'])).
% 22.92/23.16  thf('13', plain, (((sk_B_1) != (k1_xboole_0))),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf('14', plain,
% 22.92/23.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.92/23.16         ((v1_xboole_0 @ sk_C_1)
% 22.92/23.16          | ~ (v1_funct_1 @ X0)
% 22.92/23.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 22.92/23.16          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 22.92/23.16               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 22.92/23.16          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 22.92/23.16              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 22.92/23.16          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 22.92/23.16      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 22.92/23.16  thf('15', plain,
% 22.92/23.16      (![X0 : $i]:
% 22.92/23.16         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))
% 22.92/23.16          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 22.92/23.16          | ((k1_funct_1 @ 
% 22.92/23.16              (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 22.92/23.16              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 22.92/23.16          | ~ (m1_subset_1 @ sk_E @ 
% 22.92/23.16               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 22.92/23.16          | ~ (v1_funct_1 @ sk_E)
% 22.92/23.16          | (v1_xboole_0 @ sk_C_1))),
% 22.92/23.16      inference('sup-', [status(thm)], ['3', '14'])).
% 22.92/23.16  thf('16', plain,
% 22.92/23.16      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 22.92/23.16        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf('17', plain,
% 22.92/23.16      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 22.92/23.16      inference('sup-', [status(thm)], ['1', '2'])).
% 22.92/23.16  thf('18', plain,
% 22.92/23.16      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 22.92/23.16        (k1_relat_1 @ sk_E))),
% 22.92/23.16      inference('demod', [status(thm)], ['16', '17'])).
% 22.92/23.16  thf('19', plain,
% 22.92/23.16      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 22.92/23.16      inference('sup-', [status(thm)], ['7', '8'])).
% 22.92/23.16  thf('20', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 22.92/23.16      inference('demod', [status(thm)], ['18', '19'])).
% 22.92/23.16  thf('21', plain,
% 22.92/23.16      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf('22', plain, ((v1_funct_1 @ sk_E)),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf('23', plain,
% 22.92/23.16      (![X0 : $i]:
% 22.92/23.16         (~ (m1_subset_1 @ X0 @ sk_B_1)
% 22.92/23.16          | ((k1_funct_1 @ 
% 22.92/23.16              (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 22.92/23.16              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 22.92/23.16          | (v1_xboole_0 @ sk_C_1))),
% 22.92/23.16      inference('demod', [status(thm)], ['15', '20', '21', '22'])).
% 22.92/23.16  thf('24', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf('25', plain,
% 22.92/23.16      (![X0 : $i]:
% 22.92/23.16         (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 22.92/23.16            X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 22.92/23.16          | ~ (m1_subset_1 @ X0 @ sk_B_1))),
% 22.92/23.16      inference('clc', [status(thm)], ['23', '24'])).
% 22.92/23.16  thf('26', plain,
% 22.92/23.16      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 22.92/23.16         sk_F) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 22.92/23.16      inference('sup-', [status(thm)], ['0', '25'])).
% 22.92/23.16  thf('27', plain,
% 22.92/23.16      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 22.92/23.16         sk_F) != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf('28', plain,
% 22.92/23.16      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf(dt_k2_relset_1, axiom,
% 22.92/23.16    (![A:$i,B:$i,C:$i]:
% 22.92/23.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 22.92/23.16       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 22.92/23.16  thf('29', plain,
% 22.92/23.16      (![X26 : $i, X27 : $i, X28 : $i]:
% 22.92/23.16         ((m1_subset_1 @ (k2_relset_1 @ X26 @ X27 @ X28) @ (k1_zfmisc_1 @ X27))
% 22.92/23.16          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 22.92/23.16      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 22.92/23.16  thf('30', plain,
% 22.92/23.16      ((m1_subset_1 @ (k2_relset_1 @ sk_C_1 @ sk_A @ sk_E) @ 
% 22.92/23.16        (k1_zfmisc_1 @ sk_A))),
% 22.92/23.16      inference('sup-', [status(thm)], ['28', '29'])).
% 22.92/23.16  thf(t3_subset, axiom,
% 22.92/23.16    (![A:$i,B:$i]:
% 22.92/23.16     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 22.92/23.16  thf('31', plain,
% 22.92/23.16      (![X16 : $i, X17 : $i]:
% 22.92/23.16         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 22.92/23.16      inference('cnf', [status(esa)], [t3_subset])).
% 22.92/23.16  thf('32', plain, ((r1_tarski @ (k2_relset_1 @ sk_C_1 @ sk_A @ sk_E) @ sk_A)),
% 22.92/23.16      inference('sup-', [status(thm)], ['30', '31'])).
% 22.92/23.16  thf('33', plain,
% 22.92/23.16      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf('34', plain,
% 22.92/23.16      (![X32 : $i, X33 : $i, X34 : $i]:
% 22.92/23.16         (((k2_relset_1 @ X33 @ X34 @ X32) = (k2_relat_1 @ X32))
% 22.92/23.16          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 22.92/23.16      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 22.92/23.16  thf('35', plain,
% 22.92/23.16      (((k2_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k2_relat_1 @ sk_E))),
% 22.92/23.16      inference('sup-', [status(thm)], ['33', '34'])).
% 22.92/23.16  thf('36', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_A)),
% 22.92/23.16      inference('demod', [status(thm)], ['32', '35'])).
% 22.92/23.16  thf(d19_relat_1, axiom,
% 22.92/23.16    (![A:$i,B:$i]:
% 22.92/23.16     ( ( v1_relat_1 @ B ) =>
% 22.92/23.16       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 22.92/23.16  thf('37', plain,
% 22.92/23.16      (![X19 : $i, X20 : $i]:
% 22.92/23.16         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 22.92/23.16          | (v5_relat_1 @ X19 @ X20)
% 22.92/23.16          | ~ (v1_relat_1 @ X19))),
% 22.92/23.16      inference('cnf', [status(esa)], [d19_relat_1])).
% 22.92/23.16  thf('38', plain, ((~ (v1_relat_1 @ sk_E) | (v5_relat_1 @ sk_E @ sk_A))),
% 22.92/23.16      inference('sup-', [status(thm)], ['36', '37'])).
% 22.92/23.16  thf('39', plain,
% 22.92/23.16      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf(cc1_relset_1, axiom,
% 22.92/23.16    (![A:$i,B:$i,C:$i]:
% 22.92/23.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 22.92/23.16       ( v1_relat_1 @ C ) ))).
% 22.92/23.16  thf('40', plain,
% 22.92/23.16      (![X23 : $i, X24 : $i, X25 : $i]:
% 22.92/23.16         ((v1_relat_1 @ X23)
% 22.92/23.16          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 22.92/23.16      inference('cnf', [status(esa)], [cc1_relset_1])).
% 22.92/23.16  thf('41', plain, ((v1_relat_1 @ sk_E)),
% 22.92/23.16      inference('sup-', [status(thm)], ['39', '40'])).
% 22.92/23.16  thf('42', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 22.92/23.16      inference('demod', [status(thm)], ['38', '41'])).
% 22.92/23.16  thf('43', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf(t55_subset_1, axiom,
% 22.92/23.16    (![A:$i,B:$i]:
% 22.92/23.16     ( ( m1_subset_1 @ B @ A ) =>
% 22.92/23.16       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 22.92/23.16         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 22.92/23.16  thf('44', plain,
% 22.92/23.16      (![X14 : $i, X15 : $i]:
% 22.92/23.16         (((X14) = (k1_xboole_0))
% 22.92/23.16          | ~ (m1_subset_1 @ X15 @ X14)
% 22.92/23.16          | (m1_subset_1 @ (k1_tarski @ X15) @ (k1_zfmisc_1 @ X14)))),
% 22.92/23.16      inference('cnf', [status(esa)], [t55_subset_1])).
% 22.92/23.16  thf('45', plain,
% 22.92/23.16      (((m1_subset_1 @ (k1_tarski @ sk_F) @ (k1_zfmisc_1 @ sk_B_1))
% 22.92/23.16        | ((sk_B_1) = (k1_xboole_0)))),
% 22.92/23.16      inference('sup-', [status(thm)], ['43', '44'])).
% 22.92/23.16  thf('46', plain, (((sk_B_1) != (k1_xboole_0))),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf('47', plain,
% 22.92/23.16      ((m1_subset_1 @ (k1_tarski @ sk_F) @ (k1_zfmisc_1 @ sk_B_1))),
% 22.92/23.16      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 22.92/23.16  thf('48', plain,
% 22.92/23.16      (![X16 : $i, X17 : $i]:
% 22.92/23.16         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 22.92/23.16      inference('cnf', [status(esa)], [t3_subset])).
% 22.92/23.16  thf('49', plain, ((r1_tarski @ (k1_tarski @ sk_F) @ sk_B_1)),
% 22.92/23.16      inference('sup-', [status(thm)], ['47', '48'])).
% 22.92/23.16  thf(l1_zfmisc_1, axiom,
% 22.92/23.16    (![A:$i,B:$i]:
% 22.92/23.16     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 22.92/23.16  thf('50', plain,
% 22.92/23.16      (![X7 : $i, X8 : $i]:
% 22.92/23.16         ((r2_hidden @ X7 @ X8) | ~ (r1_tarski @ (k1_tarski @ X7) @ X8))),
% 22.92/23.16      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 22.92/23.16  thf('51', plain, ((r2_hidden @ sk_F @ sk_B_1)),
% 22.92/23.16      inference('sup-', [status(thm)], ['49', '50'])).
% 22.92/23.16  thf('52', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf(d1_funct_2, axiom,
% 22.92/23.16    (![A:$i,B:$i,C:$i]:
% 22.92/23.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 22.92/23.16       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 22.92/23.16           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 22.92/23.16             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 22.92/23.16         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 22.92/23.16           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 22.92/23.16             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 22.92/23.16  thf(zf_stmt_1, axiom,
% 22.92/23.16    (![C:$i,B:$i,A:$i]:
% 22.92/23.16     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 22.92/23.16       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 22.92/23.16  thf('53', plain,
% 22.92/23.16      (![X37 : $i, X38 : $i, X39 : $i]:
% 22.92/23.16         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 22.92/23.16          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 22.92/23.16          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_1])).
% 22.92/23.16  thf('54', plain,
% 22.92/23.16      ((~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1)
% 22.92/23.16        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 22.92/23.16      inference('sup-', [status(thm)], ['52', '53'])).
% 22.92/23.16  thf('55', plain,
% 22.92/23.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf('56', plain,
% 22.92/23.16      (![X29 : $i, X30 : $i, X31 : $i]:
% 22.92/23.16         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 22.92/23.16          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 22.92/23.16      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 22.92/23.16  thf('57', plain,
% 22.92/23.16      (((k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 22.92/23.16      inference('sup-', [status(thm)], ['55', '56'])).
% 22.92/23.16  thf('58', plain,
% 22.92/23.16      ((~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1)
% 22.92/23.16        | ((sk_B_1) = (k1_relat_1 @ sk_D)))),
% 22.92/23.16      inference('demod', [status(thm)], ['54', '57'])).
% 22.92/23.16  thf('59', plain,
% 22.92/23.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 22.92/23.16  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 22.92/23.16  thf(zf_stmt_4, axiom,
% 22.92/23.16    (![B:$i,A:$i]:
% 22.92/23.16     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 22.92/23.16       ( zip_tseitin_0 @ B @ A ) ))).
% 22.92/23.16  thf(zf_stmt_5, axiom,
% 22.92/23.16    (![A:$i,B:$i,C:$i]:
% 22.92/23.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 22.92/23.16       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 22.92/23.16         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 22.92/23.16           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 22.92/23.16             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 22.92/23.16  thf('60', plain,
% 22.92/23.16      (![X40 : $i, X41 : $i, X42 : $i]:
% 22.92/23.16         (~ (zip_tseitin_0 @ X40 @ X41)
% 22.92/23.16          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 22.92/23.16          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_5])).
% 22.92/23.16  thf('61', plain,
% 22.92/23.16      (((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1)
% 22.92/23.16        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_B_1))),
% 22.92/23.16      inference('sup-', [status(thm)], ['59', '60'])).
% 22.92/23.16  thf('62', plain,
% 22.92/23.16      (![X35 : $i, X36 : $i]:
% 22.92/23.16         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_4])).
% 22.92/23.16  thf(d1_xboole_0, axiom,
% 22.92/23.16    (![A:$i]:
% 22.92/23.16     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 22.92/23.16  thf('63', plain,
% 22.92/23.16      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 22.92/23.16      inference('cnf', [status(esa)], [d1_xboole_0])).
% 22.92/23.16  thf(l22_zfmisc_1, axiom,
% 22.92/23.16    (![A:$i,B:$i]:
% 22.92/23.16     ( ( r2_hidden @ A @ B ) =>
% 22.92/23.16       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 22.92/23.16  thf('64', plain,
% 22.92/23.16      (![X10 : $i, X11 : $i]:
% 22.92/23.16         (((k2_xboole_0 @ (k1_tarski @ X11) @ X10) = (X10))
% 22.92/23.16          | ~ (r2_hidden @ X11 @ X10))),
% 22.92/23.16      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 22.92/23.16  thf('65', plain,
% 22.92/23.16      (![X0 : $i]:
% 22.92/23.16         ((v1_xboole_0 @ X0)
% 22.92/23.16          | ((k2_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ X0) = (X0)))),
% 22.92/23.16      inference('sup-', [status(thm)], ['63', '64'])).
% 22.92/23.16  thf(t49_zfmisc_1, axiom,
% 22.92/23.16    (![A:$i,B:$i]:
% 22.92/23.16     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 22.92/23.16  thf('66', plain,
% 22.92/23.16      (![X12 : $i, X13 : $i]:
% 22.92/23.16         ((k2_xboole_0 @ (k1_tarski @ X12) @ X13) != (k1_xboole_0))),
% 22.92/23.16      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 22.92/23.16  thf('67', plain,
% 22.92/23.16      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (v1_xboole_0 @ X0))),
% 22.92/23.16      inference('sup-', [status(thm)], ['65', '66'])).
% 22.92/23.16  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 22.92/23.16      inference('simplify', [status(thm)], ['67'])).
% 22.92/23.16  thf('69', plain,
% 22.92/23.16      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 22.92/23.16      inference('sup+', [status(thm)], ['62', '68'])).
% 22.92/23.16  thf('70', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf('71', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C_1 @ X0)),
% 22.92/23.16      inference('sup-', [status(thm)], ['69', '70'])).
% 22.92/23.16  thf('72', plain, ((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1)),
% 22.92/23.16      inference('demod', [status(thm)], ['61', '71'])).
% 22.92/23.16  thf('73', plain, (((sk_B_1) = (k1_relat_1 @ sk_D))),
% 22.92/23.16      inference('demod', [status(thm)], ['58', '72'])).
% 22.92/23.16  thf(t12_funct_1, axiom,
% 22.92/23.16    (![A:$i,B:$i]:
% 22.92/23.16     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 22.92/23.16       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 22.92/23.16         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 22.92/23.16  thf('74', plain,
% 22.92/23.16      (![X21 : $i, X22 : $i]:
% 22.92/23.16         (~ (r2_hidden @ X21 @ (k1_relat_1 @ X22))
% 22.92/23.16          | (r2_hidden @ (k1_funct_1 @ X22 @ X21) @ (k2_relat_1 @ X22))
% 22.92/23.16          | ~ (v1_funct_1 @ X22)
% 22.92/23.16          | ~ (v1_relat_1 @ X22))),
% 22.92/23.16      inference('cnf', [status(esa)], [t12_funct_1])).
% 22.92/23.16  thf('75', plain,
% 22.92/23.16      (![X0 : $i]:
% 22.92/23.16         (~ (r2_hidden @ X0 @ sk_B_1)
% 22.92/23.16          | ~ (v1_relat_1 @ sk_D)
% 22.92/23.16          | ~ (v1_funct_1 @ sk_D)
% 22.92/23.16          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 22.92/23.16      inference('sup-', [status(thm)], ['73', '74'])).
% 22.92/23.16  thf('76', plain,
% 22.92/23.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf('77', plain,
% 22.92/23.16      (![X23 : $i, X24 : $i, X25 : $i]:
% 22.92/23.16         ((v1_relat_1 @ X23)
% 22.92/23.16          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 22.92/23.16      inference('cnf', [status(esa)], [cc1_relset_1])).
% 22.92/23.16  thf('78', plain, ((v1_relat_1 @ sk_D)),
% 22.92/23.16      inference('sup-', [status(thm)], ['76', '77'])).
% 22.92/23.16  thf('79', plain, ((v1_funct_1 @ sk_D)),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf('80', plain,
% 22.92/23.16      (![X0 : $i]:
% 22.92/23.16         (~ (r2_hidden @ X0 @ sk_B_1)
% 22.92/23.16          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 22.92/23.16      inference('demod', [status(thm)], ['75', '78', '79'])).
% 22.92/23.16  thf('81', plain,
% 22.92/23.16      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k2_relat_1 @ sk_D))),
% 22.92/23.16      inference('sup-', [status(thm)], ['51', '80'])).
% 22.92/23.16  thf('82', plain,
% 22.92/23.16      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 22.92/23.16        (k1_relat_1 @ sk_E))),
% 22.92/23.16      inference('demod', [status(thm)], ['16', '17'])).
% 22.92/23.16  thf(d3_tarski, axiom,
% 22.92/23.16    (![A:$i,B:$i]:
% 22.92/23.16     ( ( r1_tarski @ A @ B ) <=>
% 22.92/23.16       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 22.92/23.16  thf('83', plain,
% 22.92/23.16      (![X3 : $i, X4 : $i, X5 : $i]:
% 22.92/23.16         (~ (r2_hidden @ X3 @ X4)
% 22.92/23.16          | (r2_hidden @ X3 @ X5)
% 22.92/23.16          | ~ (r1_tarski @ X4 @ X5))),
% 22.92/23.16      inference('cnf', [status(esa)], [d3_tarski])).
% 22.92/23.16  thf('84', plain,
% 22.92/23.16      (![X0 : $i]:
% 22.92/23.16         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 22.92/23.16          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 22.92/23.16      inference('sup-', [status(thm)], ['82', '83'])).
% 22.92/23.16  thf('85', plain,
% 22.92/23.16      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 22.92/23.16      inference('sup-', [status(thm)], ['7', '8'])).
% 22.92/23.16  thf('86', plain,
% 22.92/23.16      (![X0 : $i]:
% 22.92/23.16         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 22.92/23.16          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 22.92/23.16      inference('demod', [status(thm)], ['84', '85'])).
% 22.92/23.16  thf('87', plain,
% 22.92/23.16      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E))),
% 22.92/23.16      inference('sup-', [status(thm)], ['81', '86'])).
% 22.92/23.16  thf(d8_partfun1, axiom,
% 22.92/23.16    (![A:$i,B:$i]:
% 22.92/23.16     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 22.92/23.16       ( ![C:$i]:
% 22.92/23.16         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 22.92/23.16           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 22.92/23.16  thf('88', plain,
% 22.92/23.16      (![X43 : $i, X44 : $i, X45 : $i]:
% 22.92/23.16         (~ (r2_hidden @ X43 @ (k1_relat_1 @ X44))
% 22.92/23.16          | ((k7_partfun1 @ X45 @ X44 @ X43) = (k1_funct_1 @ X44 @ X43))
% 22.92/23.16          | ~ (v1_funct_1 @ X44)
% 22.92/23.16          | ~ (v5_relat_1 @ X44 @ X45)
% 22.92/23.16          | ~ (v1_relat_1 @ X44))),
% 22.92/23.16      inference('cnf', [status(esa)], [d8_partfun1])).
% 22.92/23.16  thf('89', plain,
% 22.92/23.16      (![X0 : $i]:
% 22.92/23.16         (~ (v1_relat_1 @ sk_E)
% 22.92/23.16          | ~ (v5_relat_1 @ sk_E @ X0)
% 22.92/23.16          | ~ (v1_funct_1 @ sk_E)
% 22.92/23.16          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 22.92/23.16              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 22.92/23.16      inference('sup-', [status(thm)], ['87', '88'])).
% 22.92/23.16  thf('90', plain, ((v1_relat_1 @ sk_E)),
% 22.92/23.16      inference('sup-', [status(thm)], ['39', '40'])).
% 22.92/23.16  thf('91', plain, ((v1_funct_1 @ sk_E)),
% 22.92/23.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.92/23.16  thf('92', plain,
% 22.92/23.16      (![X0 : $i]:
% 22.92/23.16         (~ (v5_relat_1 @ sk_E @ X0)
% 22.92/23.16          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 22.92/23.16              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 22.92/23.16      inference('demod', [status(thm)], ['89', '90', '91'])).
% 22.92/23.16  thf('93', plain,
% 22.92/23.16      (((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 22.92/23.16         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 22.92/23.16      inference('sup-', [status(thm)], ['42', '92'])).
% 22.92/23.16  thf('94', plain,
% 22.92/23.16      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 22.92/23.16         sk_F) != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 22.92/23.16      inference('demod', [status(thm)], ['27', '93'])).
% 22.92/23.16  thf('95', plain, ($false),
% 22.92/23.16      inference('simplify_reflect-', [status(thm)], ['26', '94'])).
% 22.92/23.16  
% 22.92/23.16  % SZS output end Refutation
% 22.92/23.16  
% 22.92/23.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

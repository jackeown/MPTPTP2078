%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vKT7IZ7Bbd

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:10 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 156 expanded)
%              Number of leaves         :   36 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  955 (3314 expanded)
%              Number of equality atoms :   48 ( 141 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('8',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(clc,[status(thm)],['6','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('17',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ( X28 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X29 @ X26 ) @ ( k2_relset_1 @ X27 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('28',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('31',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( ( k7_partfun1 @ X19 @ X18 @ X17 )
        = ( k1_funct_1 @ X18 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v5_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('37',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['32','37','38'])).

thf('40',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','39'])).

thf('41',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ X21 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X21 @ X22 @ X25 @ X20 @ X24 ) @ X23 )
        = ( k1_funct_1 @ X24 @ ( k1_funct_1 @ X20 @ X23 ) ) )
      | ( X21 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X21 @ X22 @ X20 ) @ ( k1_relset_1 @ X22 @ X25 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('46',plain,(
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
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('55',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['52','55','56','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['42','60'])).

thf('62',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['41','61'])).

thf('63',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','62'])).

thf('64',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['0','64','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vKT7IZ7Bbd
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:45:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.60/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.83  % Solved by: fo/fo7.sh
% 0.60/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.83  % done 344 iterations in 0.389s
% 0.60/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.83  % SZS output start Refutation
% 0.60/0.83  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.60/0.83  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.60/0.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.83  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.60/0.83  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.83  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.60/0.83  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.60/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.83  thf(sk_E_type, type, sk_E: $i).
% 0.60/0.83  thf(sk_D_type, type, sk_D: $i).
% 0.60/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.83  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.60/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.83  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.60/0.83  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.60/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.83  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.60/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.60/0.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.83  thf(sk_F_type, type, sk_F: $i).
% 0.60/0.83  thf(t186_funct_2, conjecture,
% 0.60/0.83    (![A:$i,B:$i,C:$i]:
% 0.60/0.83     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.60/0.83       ( ![D:$i]:
% 0.60/0.83         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.60/0.83             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.60/0.83           ( ![E:$i]:
% 0.60/0.83             ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.83                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.60/0.83               ( ![F:$i]:
% 0.60/0.83                 ( ( m1_subset_1 @ F @ B ) =>
% 0.60/0.83                   ( ( r1_tarski @
% 0.60/0.83                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.60/0.83                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.60/0.83                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.60/0.83                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.60/0.83                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.83    (~( ![A:$i,B:$i,C:$i]:
% 0.60/0.83        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.60/0.83          ( ![D:$i]:
% 0.60/0.83            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.60/0.83                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.60/0.83              ( ![E:$i]:
% 0.60/0.83                ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.83                    ( m1_subset_1 @
% 0.60/0.83                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.60/0.83                  ( ![F:$i]:
% 0.60/0.83                    ( ( m1_subset_1 @ F @ B ) =>
% 0.60/0.83                      ( ( r1_tarski @
% 0.60/0.83                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.60/0.83                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.60/0.83                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.60/0.83                          ( ( k1_funct_1 @
% 0.60/0.83                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.60/0.83                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.60/0.83    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 0.60/0.83  thf('0', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('1', plain,
% 0.60/0.83      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf(cc2_relset_1, axiom,
% 0.60/0.83    (![A:$i,B:$i,C:$i]:
% 0.60/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.83       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.60/0.83  thf('2', plain,
% 0.60/0.83      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.60/0.83         ((v5_relat_1 @ X11 @ X13)
% 0.60/0.83          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.60/0.83      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.60/0.83  thf('3', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 0.60/0.83      inference('sup-', [status(thm)], ['1', '2'])).
% 0.60/0.83  thf('4', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(t2_subset, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ A @ B ) =>
% 0.60/0.84       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.60/0.84  thf('5', plain,
% 0.60/0.84      (![X5 : $i, X6 : $i]:
% 0.60/0.84         ((r2_hidden @ X5 @ X6)
% 0.60/0.84          | (v1_xboole_0 @ X6)
% 0.60/0.84          | ~ (m1_subset_1 @ X5 @ X6))),
% 0.60/0.84      inference('cnf', [status(esa)], [t2_subset])).
% 0.60/0.84  thf('6', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.60/0.84      inference('sup-', [status(thm)], ['4', '5'])).
% 0.60/0.84  thf(l13_xboole_0, axiom,
% 0.60/0.84    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.60/0.84  thf('7', plain,
% 0.60/0.84      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.60/0.84      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.60/0.84  thf('8', plain,
% 0.60/0.84      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.60/0.84      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.60/0.84  thf('9', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.60/0.84      inference('sup+', [status(thm)], ['7', '8'])).
% 0.60/0.84  thf('10', plain, (((sk_B) != (k1_xboole_0))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('11', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (((X0) != (k1_xboole_0))
% 0.60/0.84          | ~ (v1_xboole_0 @ X0)
% 0.60/0.84          | ~ (v1_xboole_0 @ sk_B))),
% 0.60/0.84      inference('sup-', [status(thm)], ['9', '10'])).
% 0.60/0.84  thf('12', plain, ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.60/0.84      inference('simplify', [status(thm)], ['11'])).
% 0.60/0.84  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.60/0.84  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.60/0.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.60/0.84  thf('14', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.60/0.84      inference('simplify_reflect+', [status(thm)], ['12', '13'])).
% 0.60/0.84  thf('15', plain, ((r2_hidden @ sk_F @ sk_B)),
% 0.60/0.84      inference('clc', [status(thm)], ['6', '14'])).
% 0.60/0.84  thf('16', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(t6_funct_2, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.84     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.60/0.84         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.84       ( ( r2_hidden @ C @ A ) =>
% 0.60/0.84         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.60/0.84           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.60/0.84  thf('17', plain,
% 0.60/0.84      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.60/0.84         (~ (r2_hidden @ X26 @ X27)
% 0.60/0.84          | ((X28) = (k1_xboole_0))
% 0.60/0.84          | ~ (v1_funct_1 @ X29)
% 0.60/0.84          | ~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.60/0.84          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.60/0.84          | (r2_hidden @ (k1_funct_1 @ X29 @ X26) @ 
% 0.60/0.84             (k2_relset_1 @ X27 @ X28 @ X29)))),
% 0.60/0.84      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.60/0.84  thf('18', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.60/0.84           (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D))
% 0.60/0.84          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C_1)
% 0.60/0.84          | ~ (v1_funct_1 @ sk_D)
% 0.60/0.84          | ((sk_C_1) = (k1_xboole_0))
% 0.60/0.84          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.60/0.84      inference('sup-', [status(thm)], ['16', '17'])).
% 0.60/0.84  thf('19', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C_1)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('21', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.60/0.84           (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D))
% 0.60/0.84          | ((sk_C_1) = (k1_xboole_0))
% 0.60/0.84          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.60/0.84      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.60/0.84  thf('22', plain,
% 0.60/0.84      ((((sk_C_1) = (k1_xboole_0))
% 0.60/0.84        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ 
% 0.60/0.84           (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['15', '21'])).
% 0.60/0.84  thf('23', plain,
% 0.60/0.84      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.60/0.84        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(d3_tarski, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( r1_tarski @ A @ B ) <=>
% 0.60/0.84       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.60/0.84  thf('24', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.84         (~ (r2_hidden @ X0 @ X1)
% 0.60/0.84          | (r2_hidden @ X0 @ X2)
% 0.60/0.84          | ~ (r1_tarski @ X1 @ X2))),
% 0.60/0.84      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.84  thf('25', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         ((r2_hidden @ X0 @ (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))
% 0.60/0.84          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['23', '24'])).
% 0.60/0.84  thf('26', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(redefinition_k1_relset_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.84       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.60/0.84  thf('27', plain,
% 0.60/0.84      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.60/0.84         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.60/0.84          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.60/0.84  thf('28', plain,
% 0.60/0.84      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.60/0.84      inference('sup-', [status(thm)], ['26', '27'])).
% 0.60/0.84  thf('29', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 0.60/0.84          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)))),
% 0.60/0.84      inference('demod', [status(thm)], ['25', '28'])).
% 0.60/0.84  thf('30', plain,
% 0.60/0.84      ((((sk_C_1) = (k1_xboole_0))
% 0.60/0.84        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['22', '29'])).
% 0.60/0.84  thf(d8_partfun1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.60/0.84       ( ![C:$i]:
% 0.60/0.84         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.60/0.84           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.60/0.84  thf('31', plain,
% 0.60/0.84      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.60/0.84         (~ (r2_hidden @ X17 @ (k1_relat_1 @ X18))
% 0.60/0.84          | ((k7_partfun1 @ X19 @ X18 @ X17) = (k1_funct_1 @ X18 @ X17))
% 0.60/0.84          | ~ (v1_funct_1 @ X18)
% 0.60/0.84          | ~ (v5_relat_1 @ X18 @ X19)
% 0.60/0.84          | ~ (v1_relat_1 @ X18))),
% 0.60/0.84      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.60/0.84  thf('32', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (((sk_C_1) = (k1_xboole_0))
% 0.60/0.84          | ~ (v1_relat_1 @ sk_E)
% 0.60/0.84          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.60/0.84          | ~ (v1_funct_1 @ sk_E)
% 0.60/0.84          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.60/0.84              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.60/0.84      inference('sup-', [status(thm)], ['30', '31'])).
% 0.60/0.84  thf('33', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(cc2_relat_1, axiom,
% 0.60/0.84    (![A:$i]:
% 0.60/0.84     ( ( v1_relat_1 @ A ) =>
% 0.60/0.84       ( ![B:$i]:
% 0.60/0.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.60/0.84  thf('34', plain,
% 0.60/0.84      (![X7 : $i, X8 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.60/0.84          | (v1_relat_1 @ X7)
% 0.60/0.84          | ~ (v1_relat_1 @ X8))),
% 0.60/0.84      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.60/0.84  thf('35', plain,
% 0.60/0.84      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) | (v1_relat_1 @ sk_E))),
% 0.60/0.84      inference('sup-', [status(thm)], ['33', '34'])).
% 0.60/0.84  thf(fc6_relat_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.60/0.84  thf('36', plain,
% 0.60/0.84      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.60/0.84      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.60/0.84  thf('37', plain, ((v1_relat_1 @ sk_E)),
% 0.60/0.84      inference('demod', [status(thm)], ['35', '36'])).
% 0.60/0.84  thf('38', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('39', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (((sk_C_1) = (k1_xboole_0))
% 0.60/0.84          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.60/0.84          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.60/0.84              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.60/0.84      inference('demod', [status(thm)], ['32', '37', '38'])).
% 0.60/0.84  thf('40', plain,
% 0.60/0.84      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.60/0.84          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.60/0.84        | ((sk_C_1) = (k1_xboole_0)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['3', '39'])).
% 0.60/0.84  thf('41', plain,
% 0.60/0.84      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.60/0.84         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('42', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('43', plain,
% 0.60/0.84      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.60/0.84      inference('sup-', [status(thm)], ['26', '27'])).
% 0.60/0.84  thf('44', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(t185_funct_2, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.60/0.84       ( ![D:$i]:
% 0.60/0.84         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.60/0.84             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.60/0.84           ( ![E:$i]:
% 0.60/0.84             ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.84                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.60/0.84               ( ![F:$i]:
% 0.60/0.84                 ( ( m1_subset_1 @ F @ B ) =>
% 0.60/0.84                   ( ( r1_tarski @
% 0.60/0.84                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.60/0.84                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.60/0.84                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.60/0.84                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.60/0.84                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.84  thf('45', plain,
% 0.60/0.84      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.60/0.84         (~ (v1_funct_1 @ X20)
% 0.60/0.84          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 0.60/0.84          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.60/0.84          | ~ (m1_subset_1 @ X23 @ X21)
% 0.60/0.84          | ((k1_funct_1 @ (k8_funct_2 @ X21 @ X22 @ X25 @ X20 @ X24) @ X23)
% 0.60/0.84              = (k1_funct_1 @ X24 @ (k1_funct_1 @ X20 @ X23)))
% 0.60/0.84          | ((X21) = (k1_xboole_0))
% 0.60/0.84          | ~ (r1_tarski @ (k2_relset_1 @ X21 @ X22 @ X20) @ 
% 0.60/0.84               (k1_relset_1 @ X22 @ X25 @ X24))
% 0.60/0.84          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X25)))
% 0.60/0.84          | ~ (v1_funct_1 @ X24)
% 0.60/0.84          | (v1_xboole_0 @ X22))),
% 0.60/0.84      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.60/0.84  thf('46', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.84         ((v1_xboole_0 @ sk_C_1)
% 0.60/0.84          | ~ (v1_funct_1 @ X0)
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.60/0.84          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.60/0.84               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.60/0.84          | ((sk_B) = (k1_xboole_0))
% 0.60/0.84          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.60/0.84              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.60/0.84          | ~ (m1_subset_1 @ X2 @ sk_B)
% 0.60/0.84          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C_1)
% 0.60/0.84          | ~ (v1_funct_1 @ sk_D))),
% 0.60/0.84      inference('sup-', [status(thm)], ['44', '45'])).
% 0.60/0.84  thf('47', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C_1)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('49', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.84         ((v1_xboole_0 @ sk_C_1)
% 0.60/0.84          | ~ (v1_funct_1 @ X0)
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.60/0.84          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.60/0.84               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.60/0.84          | ((sk_B) = (k1_xboole_0))
% 0.60/0.84          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.60/0.84              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.60/0.84          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.60/0.84      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.60/0.84  thf('50', plain, (((sk_B) != (k1_xboole_0))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('51', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.84         ((v1_xboole_0 @ sk_C_1)
% 0.60/0.84          | ~ (v1_funct_1 @ X0)
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.60/0.84          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.60/0.84               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.60/0.84          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.60/0.84              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.60/0.84          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.60/0.84      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.60/0.84  thf('52', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.60/0.84             (k1_relat_1 @ sk_E))
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.60/0.84          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.84              X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.60/0.84          | ~ (m1_subset_1 @ sk_E @ 
% 0.60/0.84               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 0.60/0.84          | ~ (v1_funct_1 @ sk_E)
% 0.60/0.84          | (v1_xboole_0 @ sk_C_1))),
% 0.60/0.84      inference('sup-', [status(thm)], ['43', '51'])).
% 0.60/0.84  thf('53', plain,
% 0.60/0.84      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.60/0.84        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('54', plain,
% 0.60/0.84      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.60/0.84      inference('sup-', [status(thm)], ['26', '27'])).
% 0.60/0.84  thf('55', plain,
% 0.60/0.84      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.60/0.84      inference('demod', [status(thm)], ['53', '54'])).
% 0.60/0.84  thf('56', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('57', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('58', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.60/0.84          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.60/0.84              X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.60/0.84          | (v1_xboole_0 @ sk_C_1))),
% 0.60/0.84      inference('demod', [status(thm)], ['52', '55', '56', '57'])).
% 0.60/0.84  thf('59', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('60', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.60/0.84            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 0.60/0.84      inference('clc', [status(thm)], ['58', '59'])).
% 0.60/0.84  thf('61', plain,
% 0.60/0.84      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.60/0.84         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['42', '60'])).
% 0.60/0.84  thf('62', plain,
% 0.60/0.84      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.60/0.84         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.60/0.84      inference('demod', [status(thm)], ['41', '61'])).
% 0.60/0.84  thf('63', plain,
% 0.60/0.84      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.60/0.84          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.60/0.84        | ((sk_C_1) = (k1_xboole_0)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['40', '62'])).
% 0.60/0.84  thf('64', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.60/0.84      inference('simplify', [status(thm)], ['63'])).
% 0.60/0.84  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.60/0.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.60/0.84  thf('66', plain, ($false),
% 0.60/0.84      inference('demod', [status(thm)], ['0', '64', '65'])).
% 0.60/0.84  
% 0.60/0.84  % SZS output end Refutation
% 0.60/0.84  
% 0.60/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

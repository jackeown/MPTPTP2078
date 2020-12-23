%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UG3m3er5LH

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:06 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 153 expanded)
%              Number of leaves         :   35 (  61 expanded)
%              Depth                    :   14
%              Number of atoms          :  941 (3300 expanded)
%              Number of equality atoms :   48 ( 141 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( X27 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X28 @ X25 ) @ ( k2_relset_1 @ X26 @ X27 @ X28 ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( ( k7_partfun1 @ X18 @ X17 @ X16 )
        = ( k1_funct_1 @ X17 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v5_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['32','35','36'])).

thf('38',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','37'])).

thf('39',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('42',plain,(
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

thf('43',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ X20 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X20 @ X21 @ X24 @ X19 @ X23 ) @ X22 )
        = ( k1_funct_1 @ X23 @ ( k1_funct_1 @ X19 @ X22 ) ) )
      | ( X20 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X20 @ X21 @ X19 ) @ ( k1_relset_1 @ X21 @ X24 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('44',plain,(
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
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf('51',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('53',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['50','53','54','55'])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['40','58'])).

thf('60',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['39','59'])).

thf('61',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','60'])).

thf('62',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['0','62','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UG3m3er5LH
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:33:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 344 iterations in 0.206s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.65  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.65  thf(sk_F_type, type, sk_F: $i).
% 0.46/0.65  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.65  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.65  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.65  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.46/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.65  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.46/0.65  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(sk_E_type, type, sk_E: $i).
% 0.46/0.65  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.65  thf(t186_funct_2, conjecture,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.46/0.65       ( ![D:$i]:
% 0.46/0.65         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.46/0.65             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.46/0.65           ( ![E:$i]:
% 0.46/0.65             ( ( ( v1_funct_1 @ E ) & 
% 0.46/0.65                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.46/0.65               ( ![F:$i]:
% 0.46/0.65                 ( ( m1_subset_1 @ F @ B ) =>
% 0.46/0.65                   ( ( r1_tarski @
% 0.46/0.65                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.46/0.65                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.46/0.65                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.46/0.65                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.46/0.65                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.65        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.46/0.65          ( ![D:$i]:
% 0.46/0.65            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.46/0.65                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.46/0.65              ( ![E:$i]:
% 0.46/0.65                ( ( ( v1_funct_1 @ E ) & 
% 0.46/0.65                    ( m1_subset_1 @
% 0.46/0.65                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.46/0.65                  ( ![F:$i]:
% 0.46/0.65                    ( ( m1_subset_1 @ F @ B ) =>
% 0.46/0.65                      ( ( r1_tarski @
% 0.46/0.65                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.46/0.65                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.46/0.65                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.46/0.65                          ( ( k1_funct_1 @
% 0.46/0.65                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.46/0.65                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 0.46/0.65  thf('0', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(cc2_relset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.65         ((v5_relat_1 @ X10 @ X12)
% 0.46/0.65          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.65  thf('3', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.65  thf('4', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t2_subset, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ A @ B ) =>
% 0.46/0.65       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (![X5 : $i, X6 : $i]:
% 0.46/0.65         ((r2_hidden @ X5 @ X6)
% 0.46/0.65          | (v1_xboole_0 @ X6)
% 0.46/0.65          | ~ (m1_subset_1 @ X5 @ X6))),
% 0.46/0.65      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.65  thf('6', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.65  thf(l13_xboole_0, axiom,
% 0.46/0.65    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.46/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.46/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['7', '8'])).
% 0.46/0.65  thf('10', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((X0) != (k1_xboole_0))
% 0.46/0.65          | ~ (v1_xboole_0 @ X0)
% 0.46/0.65          | ~ (v1_xboole_0 @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.65  thf('12', plain, ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.65  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.46/0.65  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.65  thf('14', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.46/0.65      inference('simplify_reflect+', [status(thm)], ['12', '13'])).
% 0.46/0.65  thf('15', plain, ((r2_hidden @ sk_F @ sk_B)),
% 0.46/0.65      inference('clc', [status(thm)], ['6', '14'])).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t6_funct_2, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.65     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.65       ( ( r2_hidden @ C @ A ) =>
% 0.46/0.65         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.46/0.65           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X25 @ X26)
% 0.46/0.65          | ((X27) = (k1_xboole_0))
% 0.46/0.65          | ~ (v1_funct_1 @ X28)
% 0.46/0.65          | ~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.46/0.65          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.46/0.65          | (r2_hidden @ (k1_funct_1 @ X28 @ X25) @ 
% 0.46/0.65             (k2_relset_1 @ X26 @ X27 @ X28)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.46/0.65           (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D))
% 0.46/0.65          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C_1)
% 0.46/0.65          | ~ (v1_funct_1 @ sk_D)
% 0.46/0.65          | ((sk_C_1) = (k1_xboole_0))
% 0.46/0.65          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.65  thf('19', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.46/0.65           (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D))
% 0.46/0.65          | ((sk_C_1) = (k1_xboole_0))
% 0.46/0.65          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      ((((sk_C_1) = (k1_xboole_0))
% 0.46/0.65        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ 
% 0.46/0.65           (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['15', '21'])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.46/0.65        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(d3_tarski, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.65          | (r2_hidden @ X0 @ X2)
% 0.46/0.65          | ~ (r1_tarski @ X1 @ X2))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r2_hidden @ X0 @ (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))
% 0.46/0.65          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.65         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.46/0.65          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.46/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 0.46/0.65          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)))),
% 0.46/0.65      inference('demod', [status(thm)], ['25', '28'])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      ((((sk_C_1) = (k1_xboole_0))
% 0.46/0.65        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['22', '29'])).
% 0.46/0.65  thf(d8_partfun1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.65       ( ![C:$i]:
% 0.46/0.65         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.46/0.65           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X16 @ (k1_relat_1 @ X17))
% 0.46/0.65          | ((k7_partfun1 @ X18 @ X17 @ X16) = (k1_funct_1 @ X17 @ X16))
% 0.46/0.65          | ~ (v1_funct_1 @ X17)
% 0.46/0.65          | ~ (v5_relat_1 @ X17 @ X18)
% 0.46/0.65          | ~ (v1_relat_1 @ X17))),
% 0.46/0.65      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((sk_C_1) = (k1_xboole_0))
% 0.46/0.65          | ~ (v1_relat_1 @ sk_E)
% 0.46/0.65          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ sk_E)
% 0.46/0.65          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.46/0.65              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(cc1_relset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( v1_relat_1 @ C ) ))).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.65         ((v1_relat_1 @ X7)
% 0.46/0.65          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.65  thf('35', plain, ((v1_relat_1 @ sk_E)),
% 0.46/0.65      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((sk_C_1) = (k1_xboole_0))
% 0.46/0.65          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.46/0.65          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.46/0.65              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.46/0.65      inference('demod', [status(thm)], ['32', '35', '36'])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.46/0.65          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.46/0.65        | ((sk_C_1) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['3', '37'])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.46/0.65         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('40', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('41', plain,
% 0.46/0.65      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.46/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t185_funct_2, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.46/0.65       ( ![D:$i]:
% 0.46/0.65         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.46/0.65             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.46/0.65           ( ![E:$i]:
% 0.46/0.65             ( ( ( v1_funct_1 @ E ) & 
% 0.46/0.65                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.46/0.65               ( ![F:$i]:
% 0.46/0.65                 ( ( m1_subset_1 @ F @ B ) =>
% 0.46/0.65                   ( ( r1_tarski @
% 0.46/0.65                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.46/0.65                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.46/0.65                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.46/0.65                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.46/0.65                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf('43', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.65         (~ (v1_funct_1 @ X19)
% 0.46/0.65          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 0.46/0.65          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.46/0.65          | ~ (m1_subset_1 @ X22 @ X20)
% 0.46/0.65          | ((k1_funct_1 @ (k8_funct_2 @ X20 @ X21 @ X24 @ X19 @ X23) @ X22)
% 0.46/0.65              = (k1_funct_1 @ X23 @ (k1_funct_1 @ X19 @ X22)))
% 0.46/0.65          | ((X20) = (k1_xboole_0))
% 0.46/0.65          | ~ (r1_tarski @ (k2_relset_1 @ X20 @ X21 @ X19) @ 
% 0.46/0.65               (k1_relset_1 @ X21 @ X24 @ X23))
% 0.46/0.65          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X24)))
% 0.46/0.65          | ~ (v1_funct_1 @ X23)
% 0.46/0.65          | (v1_xboole_0 @ X21))),
% 0.46/0.65      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.46/0.65  thf('44', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ sk_C_1)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.46/0.65          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.46/0.65               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.46/0.65          | ((sk_B) = (k1_xboole_0))
% 0.46/0.65          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.46/0.65              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.46/0.65          | ~ (m1_subset_1 @ X2 @ sk_B)
% 0.46/0.65          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C_1)
% 0.46/0.65          | ~ (v1_funct_1 @ sk_D))),
% 0.46/0.65      inference('sup-', [status(thm)], ['42', '43'])).
% 0.46/0.65  thf('45', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('46', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ sk_C_1)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.46/0.65          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.46/0.65               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.46/0.65          | ((sk_B) = (k1_xboole_0))
% 0.46/0.65          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.46/0.65              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.46/0.65          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.46/0.65  thf('48', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ sk_C_1)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.46/0.65          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.46/0.65               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.46/0.65          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.46/0.65              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.46/0.65          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.46/0.65  thf('50', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.46/0.65             (k1_relat_1 @ sk_E))
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.46/0.65          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.46/0.65              X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.46/0.65          | ~ (m1_subset_1 @ sk_E @ 
% 0.46/0.65               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 0.46/0.65          | ~ (v1_funct_1 @ sk_E)
% 0.46/0.65          | (v1_xboole_0 @ sk_C_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['41', '49'])).
% 0.46/0.65  thf('51', plain,
% 0.46/0.65      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.46/0.65        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.46/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.46/0.65      inference('demod', [status(thm)], ['51', '52'])).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('55', plain, ((v1_funct_1 @ sk_E)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.46/0.65          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.46/0.65              X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.46/0.65          | (v1_xboole_0 @ sk_C_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['50', '53', '54', '55'])).
% 0.46/0.65  thf('57', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.46/0.65            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 0.46/0.65      inference('clc', [status(thm)], ['56', '57'])).
% 0.46/0.65  thf('59', plain,
% 0.46/0.65      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.46/0.65         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['40', '58'])).
% 0.46/0.65  thf('60', plain,
% 0.46/0.65      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.46/0.65         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.46/0.65      inference('demod', [status(thm)], ['39', '59'])).
% 0.46/0.65  thf('61', plain,
% 0.46/0.65      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.46/0.65          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.46/0.65        | ((sk_C_1) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['38', '60'])).
% 0.46/0.65  thf('62', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['61'])).
% 0.46/0.65  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.65  thf('64', plain, ($false),
% 0.46/0.65      inference('demod', [status(thm)], ['0', '62', '63'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

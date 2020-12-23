%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p1dcveCXz3

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:10 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 153 expanded)
%              Number of leaves         :   36 (  61 expanded)
%              Depth                    :   14
%              Number of atoms          :  947 (3301 expanded)
%              Number of equality atoms :   46 ( 138 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('8',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['9'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('11',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(clc,[status(thm)],['6','12'])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ( X29 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X30 @ X27 ) @ ( k2_relset_1 @ X28 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k7_partfun1 @ X20 @ X19 @ X18 )
        = ( k1_funct_1 @ X19 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v5_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('35',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['30','35','36'])).

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
    inference('sup-',[status(thm)],['24','25'])).

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
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ X22 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X22 @ X23 @ X26 @ X21 @ X25 ) @ X24 )
        = ( k1_funct_1 @ X25 @ ( k1_funct_1 @ X21 @ X24 ) ) )
      | ( X22 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X22 @ X23 @ X21 ) @ ( k1_relset_1 @ X23 @ X26 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ( v1_xboole_0 @ X23 ) ) ),
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
    inference('sup-',[status(thm)],['24','25'])).

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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p1dcveCXz3
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.61/0.81  % Solved by: fo/fo7.sh
% 0.61/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.81  % done 344 iterations in 0.338s
% 0.61/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.61/0.81  % SZS output start Refutation
% 0.61/0.81  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.61/0.81  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.61/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.81  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.61/0.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.61/0.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.61/0.81  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.61/0.81  thf(sk_F_type, type, sk_F: $i).
% 0.61/0.81  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.61/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.81  thf(sk_E_type, type, sk_E: $i).
% 0.61/0.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.81  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.61/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.81  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.61/0.81  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.61/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.81  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.61/0.81  thf(sk_D_type, type, sk_D: $i).
% 0.61/0.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.61/0.81  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.61/0.81  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.61/0.81  thf(t186_funct_2, conjecture,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.61/0.81       ( ![D:$i]:
% 0.61/0.81         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.61/0.81             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.61/0.81           ( ![E:$i]:
% 0.61/0.81             ( ( ( v1_funct_1 @ E ) & 
% 0.61/0.81                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.61/0.81               ( ![F:$i]:
% 0.61/0.81                 ( ( m1_subset_1 @ F @ B ) =>
% 0.61/0.81                   ( ( r1_tarski @
% 0.61/0.81                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.61/0.81                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.61/0.81                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.61/0.81                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.61/0.81                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.61/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.81    (~( ![A:$i,B:$i,C:$i]:
% 0.61/0.81        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.61/0.81          ( ![D:$i]:
% 0.61/0.81            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.61/0.81                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.61/0.81              ( ![E:$i]:
% 0.61/0.81                ( ( ( v1_funct_1 @ E ) & 
% 0.61/0.81                    ( m1_subset_1 @
% 0.61/0.81                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.61/0.81                  ( ![F:$i]:
% 0.61/0.81                    ( ( m1_subset_1 @ F @ B ) =>
% 0.61/0.81                      ( ( r1_tarski @
% 0.61/0.81                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.61/0.81                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.61/0.81                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.61/0.81                          ( ( k1_funct_1 @
% 0.61/0.81                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.61/0.81                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.61/0.81    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 0.61/0.81  thf('0', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('1', plain,
% 0.61/0.81      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(cc2_relset_1, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.81       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.61/0.81  thf('2', plain,
% 0.61/0.81      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.61/0.81         ((v5_relat_1 @ X12 @ X14)
% 0.61/0.81          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.61/0.81      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.61/0.81  thf('3', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 0.61/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.61/0.81  thf('4', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(t2_subset, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( m1_subset_1 @ A @ B ) =>
% 0.61/0.81       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.61/0.81  thf('5', plain,
% 0.61/0.81      (![X6 : $i, X7 : $i]:
% 0.61/0.81         ((r2_hidden @ X6 @ X7)
% 0.61/0.81          | (v1_xboole_0 @ X7)
% 0.61/0.81          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.61/0.81      inference('cnf', [status(esa)], [t2_subset])).
% 0.61/0.81  thf('6', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.61/0.81      inference('sup-', [status(thm)], ['4', '5'])).
% 0.61/0.81  thf(t8_boole, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.61/0.81  thf('7', plain,
% 0.61/0.81      (![X4 : $i, X5 : $i]:
% 0.61/0.81         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t8_boole])).
% 0.61/0.81  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('9', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (((X0) != (k1_xboole_0))
% 0.61/0.81          | ~ (v1_xboole_0 @ sk_B)
% 0.61/0.81          | ~ (v1_xboole_0 @ X0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['7', '8'])).
% 0.61/0.81  thf('10', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B))),
% 0.61/0.81      inference('simplify', [status(thm)], ['9'])).
% 0.61/0.81  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.61/0.81  thf('11', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.61/0.81  thf('12', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.61/0.81      inference('simplify_reflect+', [status(thm)], ['10', '11'])).
% 0.61/0.81  thf('13', plain, ((r2_hidden @ sk_F @ sk_B)),
% 0.61/0.81      inference('clc', [status(thm)], ['6', '12'])).
% 0.61/0.81  thf('14', plain,
% 0.61/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(t6_funct_2, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.81     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.61/0.81         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.81       ( ( r2_hidden @ C @ A ) =>
% 0.61/0.81         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.61/0.81           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.61/0.81  thf('15', plain,
% 0.61/0.81      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X27 @ X28)
% 0.61/0.81          | ((X29) = (k1_xboole_0))
% 0.61/0.81          | ~ (v1_funct_1 @ X30)
% 0.61/0.81          | ~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.61/0.81          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.61/0.81          | (r2_hidden @ (k1_funct_1 @ X30 @ X27) @ 
% 0.61/0.81             (k2_relset_1 @ X28 @ X29 @ X30)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.61/0.81  thf('16', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.61/0.81           (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D))
% 0.61/0.81          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C_1)
% 0.61/0.81          | ~ (v1_funct_1 @ sk_D)
% 0.61/0.81          | ((sk_C_1) = (k1_xboole_0))
% 0.61/0.81          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.61/0.81      inference('sup-', [status(thm)], ['14', '15'])).
% 0.61/0.81  thf('17', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C_1)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('19', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.61/0.81           (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D))
% 0.61/0.81          | ((sk_C_1) = (k1_xboole_0))
% 0.61/0.81          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.61/0.81      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.61/0.81  thf('20', plain,
% 0.61/0.81      ((((sk_C_1) = (k1_xboole_0))
% 0.61/0.81        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ 
% 0.61/0.81           (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['13', '19'])).
% 0.61/0.81  thf('21', plain,
% 0.61/0.81      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.61/0.81        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(d3_tarski, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( r1_tarski @ A @ B ) <=>
% 0.61/0.81       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.61/0.81  thf('22', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X0 @ X1)
% 0.61/0.81          | (r2_hidden @ X0 @ X2)
% 0.61/0.81          | ~ (r1_tarski @ X1 @ X2))),
% 0.61/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.81  thf('23', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((r2_hidden @ X0 @ (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))
% 0.61/0.81          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['21', '22'])).
% 0.61/0.81  thf('24', plain,
% 0.61/0.81      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(redefinition_k1_relset_1, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.81       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.61/0.81  thf('25', plain,
% 0.61/0.81      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.61/0.81         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.61/0.81          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.61/0.81      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.61/0.81  thf('26', plain,
% 0.61/0.81      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.61/0.81      inference('sup-', [status(thm)], ['24', '25'])).
% 0.61/0.81  thf('27', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 0.61/0.81          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)))),
% 0.61/0.81      inference('demod', [status(thm)], ['23', '26'])).
% 0.61/0.81  thf('28', plain,
% 0.61/0.81      ((((sk_C_1) = (k1_xboole_0))
% 0.61/0.81        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['20', '27'])).
% 0.61/0.81  thf(d8_partfun1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.61/0.81       ( ![C:$i]:
% 0.61/0.81         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.61/0.81           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.61/0.81  thf('29', plain,
% 0.61/0.81      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X18 @ (k1_relat_1 @ X19))
% 0.61/0.81          | ((k7_partfun1 @ X20 @ X19 @ X18) = (k1_funct_1 @ X19 @ X18))
% 0.61/0.81          | ~ (v1_funct_1 @ X19)
% 0.61/0.81          | ~ (v5_relat_1 @ X19 @ X20)
% 0.61/0.81          | ~ (v1_relat_1 @ X19))),
% 0.61/0.81      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.61/0.81  thf('30', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (((sk_C_1) = (k1_xboole_0))
% 0.61/0.81          | ~ (v1_relat_1 @ sk_E)
% 0.61/0.81          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.61/0.81          | ~ (v1_funct_1 @ sk_E)
% 0.61/0.81          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.61/0.81              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.61/0.81      inference('sup-', [status(thm)], ['28', '29'])).
% 0.61/0.81  thf('31', plain,
% 0.61/0.81      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(cc2_relat_1, axiom,
% 0.61/0.81    (![A:$i]:
% 0.61/0.81     ( ( v1_relat_1 @ A ) =>
% 0.61/0.81       ( ![B:$i]:
% 0.61/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.61/0.81  thf('32', plain,
% 0.61/0.81      (![X8 : $i, X9 : $i]:
% 0.61/0.81         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.61/0.81          | (v1_relat_1 @ X8)
% 0.61/0.81          | ~ (v1_relat_1 @ X9))),
% 0.61/0.81      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.61/0.81  thf('33', plain,
% 0.61/0.81      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) | (v1_relat_1 @ sk_E))),
% 0.61/0.81      inference('sup-', [status(thm)], ['31', '32'])).
% 0.61/0.81  thf(fc6_relat_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.61/0.81  thf('34', plain,
% 0.61/0.81      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.61/0.81      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.61/0.81  thf('35', plain, ((v1_relat_1 @ sk_E)),
% 0.61/0.81      inference('demod', [status(thm)], ['33', '34'])).
% 0.61/0.81  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('37', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (((sk_C_1) = (k1_xboole_0))
% 0.61/0.81          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.61/0.81          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.61/0.81              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.61/0.81      inference('demod', [status(thm)], ['30', '35', '36'])).
% 0.61/0.81  thf('38', plain,
% 0.61/0.81      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.61/0.81          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.61/0.81        | ((sk_C_1) = (k1_xboole_0)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['3', '37'])).
% 0.61/0.81  thf('39', plain,
% 0.61/0.81      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.61/0.81         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('40', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('41', plain,
% 0.61/0.81      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.61/0.81      inference('sup-', [status(thm)], ['24', '25'])).
% 0.61/0.81  thf('42', plain,
% 0.61/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(t185_funct_2, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.61/0.81       ( ![D:$i]:
% 0.61/0.81         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.61/0.81             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.61/0.81           ( ![E:$i]:
% 0.61/0.81             ( ( ( v1_funct_1 @ E ) & 
% 0.61/0.81                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.61/0.81               ( ![F:$i]:
% 0.61/0.81                 ( ( m1_subset_1 @ F @ B ) =>
% 0.61/0.81                   ( ( r1_tarski @
% 0.61/0.81                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.61/0.81                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.61/0.81                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.61/0.81                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.61/0.81                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.61/0.81  thf('43', plain,
% 0.61/0.81      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.61/0.81         (~ (v1_funct_1 @ X21)
% 0.61/0.81          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.61/0.81          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.61/0.81          | ~ (m1_subset_1 @ X24 @ X22)
% 0.61/0.81          | ((k1_funct_1 @ (k8_funct_2 @ X22 @ X23 @ X26 @ X21 @ X25) @ X24)
% 0.61/0.81              = (k1_funct_1 @ X25 @ (k1_funct_1 @ X21 @ X24)))
% 0.61/0.81          | ((X22) = (k1_xboole_0))
% 0.61/0.81          | ~ (r1_tarski @ (k2_relset_1 @ X22 @ X23 @ X21) @ 
% 0.61/0.81               (k1_relset_1 @ X23 @ X26 @ X25))
% 0.61/0.81          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X26)))
% 0.61/0.81          | ~ (v1_funct_1 @ X25)
% 0.61/0.81          | (v1_xboole_0 @ X23))),
% 0.61/0.81      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.61/0.81  thf('44', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.81         ((v1_xboole_0 @ sk_C_1)
% 0.61/0.81          | ~ (v1_funct_1 @ X0)
% 0.61/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.61/0.81          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.61/0.81               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.61/0.81          | ((sk_B) = (k1_xboole_0))
% 0.61/0.81          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.61/0.81              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.61/0.81          | ~ (m1_subset_1 @ X2 @ sk_B)
% 0.61/0.81          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C_1)
% 0.61/0.81          | ~ (v1_funct_1 @ sk_D))),
% 0.61/0.81      inference('sup-', [status(thm)], ['42', '43'])).
% 0.61/0.81  thf('45', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C_1)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('46', plain, ((v1_funct_1 @ sk_D)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('47', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.81         ((v1_xboole_0 @ sk_C_1)
% 0.61/0.81          | ~ (v1_funct_1 @ X0)
% 0.61/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.61/0.81          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.61/0.81               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.61/0.81          | ((sk_B) = (k1_xboole_0))
% 0.61/0.81          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.61/0.81              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.61/0.81          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.61/0.81      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.61/0.81  thf('48', plain, (((sk_B) != (k1_xboole_0))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('49', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.81         ((v1_xboole_0 @ sk_C_1)
% 0.61/0.81          | ~ (v1_funct_1 @ X0)
% 0.61/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.61/0.81          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.61/0.81               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.61/0.81          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.61/0.81              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.61/0.81          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.61/0.81      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.61/0.81  thf('50', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.61/0.81             (k1_relat_1 @ sk_E))
% 0.61/0.81          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.61/0.81          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.61/0.81              X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.61/0.81          | ~ (m1_subset_1 @ sk_E @ 
% 0.61/0.81               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 0.61/0.81          | ~ (v1_funct_1 @ sk_E)
% 0.61/0.81          | (v1_xboole_0 @ sk_C_1))),
% 0.61/0.81      inference('sup-', [status(thm)], ['41', '49'])).
% 0.61/0.81  thf('51', plain,
% 0.61/0.81      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 0.61/0.81        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('52', plain,
% 0.61/0.81      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.61/0.81      inference('sup-', [status(thm)], ['24', '25'])).
% 0.61/0.81  thf('53', plain,
% 0.61/0.81      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.61/0.81      inference('demod', [status(thm)], ['51', '52'])).
% 0.61/0.81  thf('54', plain,
% 0.61/0.81      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('55', plain, ((v1_funct_1 @ sk_E)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('56', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.61/0.81          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.61/0.81              X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.61/0.81          | (v1_xboole_0 @ sk_C_1))),
% 0.61/0.81      inference('demod', [status(thm)], ['50', '53', '54', '55'])).
% 0.61/0.81  thf('57', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('58', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.61/0.81            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.61/0.81          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 0.61/0.81      inference('clc', [status(thm)], ['56', '57'])).
% 0.61/0.81  thf('59', plain,
% 0.61/0.81      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.61/0.81         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['40', '58'])).
% 0.61/0.81  thf('60', plain,
% 0.61/0.81      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.61/0.81         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.61/0.81      inference('demod', [status(thm)], ['39', '59'])).
% 0.61/0.81  thf('61', plain,
% 0.61/0.81      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.61/0.81          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.61/0.81        | ((sk_C_1) = (k1_xboole_0)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['38', '60'])).
% 0.61/0.81  thf('62', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.61/0.81      inference('simplify', [status(thm)], ['61'])).
% 0.61/0.81  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.61/0.81  thf('64', plain, ($false),
% 0.61/0.81      inference('demod', [status(thm)], ['0', '62', '63'])).
% 0.61/0.81  
% 0.61/0.81  % SZS output end Refutation
% 0.61/0.81  
% 0.61/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

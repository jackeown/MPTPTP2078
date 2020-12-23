%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4mGmma3W1Y

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:05 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 163 expanded)
%              Number of leaves         :   37 (  65 expanded)
%              Depth                    :   16
%              Number of atoms          :  980 (3370 expanded)
%              Number of equality atoms :   48 ( 140 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['16','17'])).

thf('19',plain,(
    r2_hidden @ sk_F @ sk_B_1 ),
    inference(clc,[status(thm)],['6','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('21',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ( X32 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X33 @ X30 ) @ ( k2_relset_1 @ X31 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('32',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('35',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( ( k7_partfun1 @ X23 @ X22 @ X21 )
        = ( k1_funct_1 @ X22 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v5_relat_1 @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['36','39','40'])).

thf('42',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','41'])).

thf('43',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ X25 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X25 @ X26 @ X29 @ X24 @ X28 ) @ X27 )
        = ( k1_funct_1 @ X28 @ ( k1_funct_1 @ X24 @ X27 ) ) )
      | ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X25 @ X26 @ X24 ) @ ( k1_relset_1 @ X26 @ X29 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('48',plain,(
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
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['45','53'])).

thf('55',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('57',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['54','57','58','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['44','62'])).

thf('64',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['43','63'])).

thf('65',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','64'])).

thf('66',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['0','66','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4mGmma3W1Y
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:43:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.54/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.72  % Solved by: fo/fo7.sh
% 0.54/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.72  % done 458 iterations in 0.264s
% 0.54/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.72  % SZS output start Refutation
% 0.54/0.72  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.54/0.72  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.54/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.72  thf(sk_F_type, type, sk_F: $i).
% 0.54/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.72  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.54/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.72  thf(sk_E_type, type, sk_E: $i).
% 0.54/0.72  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.54/0.72  thf(sk_D_type, type, sk_D: $i).
% 0.54/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.72  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.54/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.72  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.54/0.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.54/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.73  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.54/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.73  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.54/0.73  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.54/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.73  thf(t186_funct_2, conjecture,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.54/0.73       ( ![D:$i]:
% 0.54/0.73         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.54/0.73             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.54/0.73           ( ![E:$i]:
% 0.54/0.73             ( ( ( v1_funct_1 @ E ) & 
% 0.54/0.73                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.54/0.73               ( ![F:$i]:
% 0.54/0.73                 ( ( m1_subset_1 @ F @ B ) =>
% 0.54/0.73                   ( ( r1_tarski @
% 0.54/0.73                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.54/0.73                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.54/0.73                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.54/0.73                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.54/0.73                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.54/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.73        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.54/0.73          ( ![D:$i]:
% 0.54/0.73            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.54/0.73                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.54/0.73              ( ![E:$i]:
% 0.54/0.73                ( ( ( v1_funct_1 @ E ) & 
% 0.54/0.73                    ( m1_subset_1 @
% 0.54/0.73                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.54/0.73                  ( ![F:$i]:
% 0.54/0.73                    ( ( m1_subset_1 @ F @ B ) =>
% 0.54/0.73                      ( ( r1_tarski @
% 0.54/0.73                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.54/0.73                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.54/0.73                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.54/0.73                          ( ( k1_funct_1 @
% 0.54/0.73                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.54/0.73                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.54/0.73    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 0.54/0.73  thf('0', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('1', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(cc2_relset_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.73       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.54/0.73  thf('2', plain,
% 0.54/0.73      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.54/0.73         ((v5_relat_1 @ X15 @ X17)
% 0.54/0.73          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.54/0.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.73  thf('3', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 0.54/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.73  thf('4', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(t2_subset, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( m1_subset_1 @ A @ B ) =>
% 0.54/0.73       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.54/0.73  thf('5', plain,
% 0.54/0.73      (![X10 : $i, X11 : $i]:
% 0.54/0.73         ((r2_hidden @ X10 @ X11)
% 0.54/0.73          | (v1_xboole_0 @ X11)
% 0.54/0.73          | ~ (m1_subset_1 @ X10 @ X11))),
% 0.54/0.73      inference('cnf', [status(esa)], [t2_subset])).
% 0.54/0.73  thf('6', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['4', '5'])).
% 0.54/0.73  thf(d3_tarski, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( r1_tarski @ A @ B ) <=>
% 0.54/0.73       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.54/0.73  thf('7', plain,
% 0.54/0.73      (![X4 : $i, X6 : $i]:
% 0.54/0.73         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.73  thf(d1_xboole_0, axiom,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.54/0.73  thf('8', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.54/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.54/0.73  thf('9', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['7', '8'])).
% 0.54/0.73  thf('10', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['7', '8'])).
% 0.54/0.73  thf(d10_xboole_0, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.73  thf('11', plain,
% 0.54/0.73      (![X7 : $i, X9 : $i]:
% 0.54/0.73         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.54/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.73  thf('12', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['10', '11'])).
% 0.54/0.73  thf('13', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['9', '12'])).
% 0.54/0.73  thf('14', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('15', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (((X0) != (k1_xboole_0))
% 0.54/0.73          | ~ (v1_xboole_0 @ sk_B_1)
% 0.54/0.73          | ~ (v1_xboole_0 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['13', '14'])).
% 0.54/0.73  thf('16', plain,
% 0.54/0.73      ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.54/0.73      inference('simplify', [status(thm)], ['15'])).
% 0.54/0.73  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.54/0.73  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.73  thf('18', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.54/0.73      inference('simplify_reflect+', [status(thm)], ['16', '17'])).
% 0.54/0.73  thf('19', plain, ((r2_hidden @ sk_F @ sk_B_1)),
% 0.54/0.73      inference('clc', [status(thm)], ['6', '18'])).
% 0.54/0.73  thf('20', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(t6_funct_2, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.73     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.54/0.73         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.73       ( ( r2_hidden @ C @ A ) =>
% 0.54/0.73         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.54/0.73           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.54/0.73  thf('21', plain,
% 0.54/0.73      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.54/0.73         (~ (r2_hidden @ X30 @ X31)
% 0.54/0.73          | ((X32) = (k1_xboole_0))
% 0.54/0.73          | ~ (v1_funct_1 @ X33)
% 0.54/0.73          | ~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.54/0.73          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.54/0.73          | (r2_hidden @ (k1_funct_1 @ X33 @ X30) @ 
% 0.54/0.73             (k2_relset_1 @ X31 @ X32 @ X33)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.54/0.73  thf('22', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.54/0.73           (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D))
% 0.54/0.73          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 0.54/0.73          | ~ (v1_funct_1 @ sk_D)
% 0.54/0.73          | ((sk_C_1) = (k1_xboole_0))
% 0.54/0.73          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['20', '21'])).
% 0.54/0.73  thf('23', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('24', plain, ((v1_funct_1 @ sk_D)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('25', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.54/0.73           (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D))
% 0.54/0.73          | ((sk_C_1) = (k1_xboole_0))
% 0.54/0.73          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.54/0.73      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.54/0.73  thf('26', plain,
% 0.54/0.73      ((((sk_C_1) = (k1_xboole_0))
% 0.54/0.73        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ 
% 0.54/0.73           (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['19', '25'])).
% 0.54/0.73  thf('27', plain,
% 0.54/0.73      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.54/0.73        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('28', plain,
% 0.54/0.73      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.73         (~ (r2_hidden @ X3 @ X4)
% 0.54/0.73          | (r2_hidden @ X3 @ X5)
% 0.54/0.73          | ~ (r1_tarski @ X4 @ X5))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.73  thf('29', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((r2_hidden @ X0 @ (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))
% 0.54/0.73          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['27', '28'])).
% 0.54/0.73  thf('30', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(redefinition_k1_relset_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.73       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.54/0.73  thf('31', plain,
% 0.54/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.73         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.54/0.73          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.54/0.73      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.54/0.73  thf('32', plain,
% 0.54/0.73      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.54/0.73      inference('sup-', [status(thm)], ['30', '31'])).
% 0.54/0.73  thf('33', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 0.54/0.73          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.54/0.73      inference('demod', [status(thm)], ['29', '32'])).
% 0.54/0.73  thf('34', plain,
% 0.54/0.73      ((((sk_C_1) = (k1_xboole_0))
% 0.54/0.73        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['26', '33'])).
% 0.54/0.73  thf(d8_partfun1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.73       ( ![C:$i]:
% 0.54/0.73         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.54/0.73           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.54/0.73  thf('35', plain,
% 0.54/0.73      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.54/0.73         (~ (r2_hidden @ X21 @ (k1_relat_1 @ X22))
% 0.54/0.73          | ((k7_partfun1 @ X23 @ X22 @ X21) = (k1_funct_1 @ X22 @ X21))
% 0.54/0.73          | ~ (v1_funct_1 @ X22)
% 0.54/0.73          | ~ (v5_relat_1 @ X22 @ X23)
% 0.54/0.73          | ~ (v1_relat_1 @ X22))),
% 0.54/0.73      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.54/0.73  thf('36', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (((sk_C_1) = (k1_xboole_0))
% 0.54/0.73          | ~ (v1_relat_1 @ sk_E)
% 0.54/0.73          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.54/0.73          | ~ (v1_funct_1 @ sk_E)
% 0.54/0.73          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.54/0.73              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['34', '35'])).
% 0.54/0.73  thf('37', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(cc1_relset_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.73       ( v1_relat_1 @ C ) ))).
% 0.54/0.73  thf('38', plain,
% 0.54/0.73      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.54/0.73         ((v1_relat_1 @ X12)
% 0.54/0.73          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.54/0.73      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.54/0.73  thf('39', plain, ((v1_relat_1 @ sk_E)),
% 0.54/0.73      inference('sup-', [status(thm)], ['37', '38'])).
% 0.54/0.73  thf('40', plain, ((v1_funct_1 @ sk_E)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('41', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (((sk_C_1) = (k1_xboole_0))
% 0.54/0.73          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.54/0.73          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.54/0.73              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.54/0.73      inference('demod', [status(thm)], ['36', '39', '40'])).
% 0.54/0.73  thf('42', plain,
% 0.54/0.73      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.54/0.73          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.54/0.73        | ((sk_C_1) = (k1_xboole_0)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['3', '41'])).
% 0.54/0.73  thf('43', plain,
% 0.54/0.73      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.54/0.73         sk_F) != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('44', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('45', plain,
% 0.54/0.73      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.54/0.73      inference('sup-', [status(thm)], ['30', '31'])).
% 0.54/0.73  thf('46', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(t185_funct_2, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.54/0.73       ( ![D:$i]:
% 0.54/0.73         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.54/0.73             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.54/0.73           ( ![E:$i]:
% 0.54/0.73             ( ( ( v1_funct_1 @ E ) & 
% 0.54/0.73                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.54/0.73               ( ![F:$i]:
% 0.54/0.73                 ( ( m1_subset_1 @ F @ B ) =>
% 0.54/0.73                   ( ( r1_tarski @
% 0.54/0.73                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.54/0.73                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.54/0.73                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.54/0.73                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.54/0.73                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.54/0.73  thf('47', plain,
% 0.54/0.73      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.54/0.73         (~ (v1_funct_1 @ X24)
% 0.54/0.73          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.54/0.73          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.54/0.73          | ~ (m1_subset_1 @ X27 @ X25)
% 0.54/0.73          | ((k1_funct_1 @ (k8_funct_2 @ X25 @ X26 @ X29 @ X24 @ X28) @ X27)
% 0.54/0.73              = (k1_funct_1 @ X28 @ (k1_funct_1 @ X24 @ X27)))
% 0.54/0.73          | ((X25) = (k1_xboole_0))
% 0.54/0.73          | ~ (r1_tarski @ (k2_relset_1 @ X25 @ X26 @ X24) @ 
% 0.54/0.73               (k1_relset_1 @ X26 @ X29 @ X28))
% 0.54/0.73          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X29)))
% 0.54/0.73          | ~ (v1_funct_1 @ X28)
% 0.54/0.73          | (v1_xboole_0 @ X26))),
% 0.54/0.73      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.54/0.73  thf('48', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.73         ((v1_xboole_0 @ sk_C_1)
% 0.54/0.73          | ~ (v1_funct_1 @ X0)
% 0.54/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.54/0.73          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.54/0.73               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.54/0.73          | ((sk_B_1) = (k1_xboole_0))
% 0.54/0.73          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.54/0.73              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.54/0.73          | ~ (m1_subset_1 @ X2 @ sk_B_1)
% 0.54/0.73          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 0.54/0.73          | ~ (v1_funct_1 @ sk_D))),
% 0.54/0.73      inference('sup-', [status(thm)], ['46', '47'])).
% 0.54/0.73  thf('49', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('50', plain, ((v1_funct_1 @ sk_D)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('51', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.73         ((v1_xboole_0 @ sk_C_1)
% 0.54/0.73          | ~ (v1_funct_1 @ X0)
% 0.54/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.54/0.73          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.54/0.73               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.54/0.73          | ((sk_B_1) = (k1_xboole_0))
% 0.54/0.73          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.54/0.73              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.54/0.73          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 0.54/0.73      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.54/0.73  thf('52', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('53', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.73         ((v1_xboole_0 @ sk_C_1)
% 0.54/0.73          | ~ (v1_funct_1 @ X0)
% 0.54/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.54/0.73          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.54/0.73               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.54/0.73          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.54/0.73              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.54/0.73          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 0.54/0.73      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 0.54/0.73  thf('54', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.54/0.73             (k1_relat_1 @ sk_E))
% 0.54/0.73          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.54/0.73          | ((k1_funct_1 @ 
% 0.54/0.73              (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.54/0.73              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.54/0.73          | ~ (m1_subset_1 @ sk_E @ 
% 0.54/0.73               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 0.54/0.73          | ~ (v1_funct_1 @ sk_E)
% 0.54/0.73          | (v1_xboole_0 @ sk_C_1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['45', '53'])).
% 0.54/0.73  thf('55', plain,
% 0.54/0.73      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.54/0.73        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('56', plain,
% 0.54/0.73      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.54/0.73      inference('sup-', [status(thm)], ['30', '31'])).
% 0.54/0.73  thf('57', plain,
% 0.54/0.73      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.54/0.73        (k1_relat_1 @ sk_E))),
% 0.54/0.73      inference('demod', [status(thm)], ['55', '56'])).
% 0.54/0.73  thf('58', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('59', plain, ((v1_funct_1 @ sk_E)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('60', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.54/0.73          | ((k1_funct_1 @ 
% 0.54/0.73              (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.54/0.73              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.54/0.73          | (v1_xboole_0 @ sk_C_1))),
% 0.54/0.73      inference('demod', [status(thm)], ['54', '57', '58', '59'])).
% 0.54/0.73  thf('61', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('62', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.54/0.73            X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.54/0.73          | ~ (m1_subset_1 @ X0 @ sk_B_1))),
% 0.54/0.73      inference('clc', [status(thm)], ['60', '61'])).
% 0.54/0.73  thf('63', plain,
% 0.54/0.73      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.54/0.73         sk_F) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['44', '62'])).
% 0.54/0.73  thf('64', plain,
% 0.54/0.73      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.54/0.73         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.54/0.73      inference('demod', [status(thm)], ['43', '63'])).
% 0.54/0.73  thf('65', plain,
% 0.54/0.73      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.54/0.73          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.54/0.73        | ((sk_C_1) = (k1_xboole_0)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['42', '64'])).
% 0.54/0.73  thf('66', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.54/0.73      inference('simplify', [status(thm)], ['65'])).
% 0.54/0.73  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.73  thf('68', plain, ($false),
% 0.54/0.73      inference('demod', [status(thm)], ['0', '66', '67'])).
% 0.54/0.73  
% 0.54/0.73  % SZS output end Refutation
% 0.54/0.73  
% 0.54/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

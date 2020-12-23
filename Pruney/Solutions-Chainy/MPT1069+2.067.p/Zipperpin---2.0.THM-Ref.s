%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IaplC7RcVs

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:10 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 196 expanded)
%              Number of leaves         :   40 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          : 1054 (3572 expanded)
%              Number of equality atoms :   49 ( 142 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ( X32 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X33 @ X30 ) @ ( k2_relset_1 @ X31 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('15',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('24',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( sk_B @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('27',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','32'])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['19','33'])).

thf('35',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['13','34'])).

thf('36',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('41',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('44',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( ( k7_partfun1 @ X23 @ X22 @ X21 )
        = ( k1_funct_1 @ X22 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v5_relat_1 @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('49',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('50',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['45','50','51'])).

thf('53',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','52'])).

thf('54',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('57',plain,(
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

thf('58',plain,(
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

thf('59',plain,(
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
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['56','64'])).

thf('66',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('68',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['65','68','69','70'])).

thf('72',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['55','73'])).

thf('75',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['54','74'])).

thf('76',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','75'])).

thf('77',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','32'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['0','77','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IaplC7RcVs
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:06:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.55/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.73  % Solved by: fo/fo7.sh
% 0.55/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.73  % done 572 iterations in 0.265s
% 0.55/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.73  % SZS output start Refutation
% 0.55/0.73  thf(sk_F_type, type, sk_F: $i).
% 0.55/0.73  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.55/0.73  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.55/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.55/0.73  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.55/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.73  thf(sk_B_type, type, sk_B: $i > $i).
% 0.55/0.73  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.55/0.73  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.55/0.73  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.55/0.73  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.55/0.73  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.55/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.73  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.55/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.73  thf(sk_D_type, type, sk_D: $i).
% 0.55/0.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.55/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.55/0.73  thf(sk_E_type, type, sk_E: $i).
% 0.55/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.73  thf(t186_funct_2, conjecture,
% 0.55/0.73    (![A:$i,B:$i,C:$i]:
% 0.55/0.73     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.55/0.73       ( ![D:$i]:
% 0.55/0.73         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.55/0.73             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.55/0.73           ( ![E:$i]:
% 0.55/0.73             ( ( ( v1_funct_1 @ E ) & 
% 0.55/0.73                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.55/0.73               ( ![F:$i]:
% 0.55/0.73                 ( ( m1_subset_1 @ F @ B ) =>
% 0.55/0.73                   ( ( r1_tarski @
% 0.55/0.73                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.55/0.73                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.55/0.73                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.55/0.73                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.55/0.73                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.55/0.73        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.55/0.73          ( ![D:$i]:
% 0.55/0.73            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.55/0.73                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.55/0.73              ( ![E:$i]:
% 0.55/0.73                ( ( ( v1_funct_1 @ E ) & 
% 0.55/0.73                    ( m1_subset_1 @
% 0.55/0.73                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.55/0.73                  ( ![F:$i]:
% 0.55/0.73                    ( ( m1_subset_1 @ F @ B ) =>
% 0.55/0.73                      ( ( r1_tarski @
% 0.55/0.73                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.55/0.73                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.55/0.73                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.55/0.73                          ( ( k1_funct_1 @
% 0.55/0.73                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.55/0.73                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.55/0.73    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 0.55/0.73  thf('0', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('1', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(cc2_relset_1, axiom,
% 0.55/0.73    (![A:$i,B:$i,C:$i]:
% 0.55/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.73       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.55/0.73  thf('2', plain,
% 0.55/0.73      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.55/0.73         ((v5_relat_1 @ X15 @ X17)
% 0.55/0.73          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.55/0.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.55/0.73  thf('3', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 0.55/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.73  thf('4', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(t2_subset, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( m1_subset_1 @ A @ B ) =>
% 0.55/0.73       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.55/0.73  thf('5', plain,
% 0.55/0.73      (![X7 : $i, X8 : $i]:
% 0.55/0.73         ((r2_hidden @ X7 @ X8)
% 0.55/0.73          | (v1_xboole_0 @ X8)
% 0.55/0.73          | ~ (m1_subset_1 @ X7 @ X8))),
% 0.55/0.73      inference('cnf', [status(esa)], [t2_subset])).
% 0.55/0.73  thf('6', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 0.55/0.73      inference('sup-', [status(thm)], ['4', '5'])).
% 0.55/0.73  thf('7', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(t6_funct_2, axiom,
% 0.55/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.73     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.55/0.73         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.73       ( ( r2_hidden @ C @ A ) =>
% 0.55/0.73         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.55/0.73           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.55/0.73  thf('8', plain,
% 0.55/0.73      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.55/0.73         (~ (r2_hidden @ X30 @ X31)
% 0.55/0.73          | ((X32) = (k1_xboole_0))
% 0.55/0.73          | ~ (v1_funct_1 @ X33)
% 0.55/0.73          | ~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.55/0.73          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.55/0.73          | (r2_hidden @ (k1_funct_1 @ X33 @ X30) @ 
% 0.55/0.73             (k2_relset_1 @ X31 @ X32 @ X33)))),
% 0.55/0.73      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.55/0.73  thf('9', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.55/0.73           (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D))
% 0.55/0.73          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 0.55/0.73          | ~ (v1_funct_1 @ sk_D)
% 0.55/0.73          | ((sk_C_1) = (k1_xboole_0))
% 0.55/0.73          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.55/0.73      inference('sup-', [status(thm)], ['7', '8'])).
% 0.55/0.73  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('12', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.55/0.73           (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D))
% 0.55/0.73          | ((sk_C_1) = (k1_xboole_0))
% 0.55/0.73          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.55/0.73      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.55/0.73  thf('13', plain,
% 0.55/0.73      (((v1_xboole_0 @ sk_B_1)
% 0.55/0.73        | ((sk_C_1) = (k1_xboole_0))
% 0.55/0.73        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ 
% 0.55/0.73           (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['6', '12'])).
% 0.55/0.73  thf(l13_xboole_0, axiom,
% 0.55/0.73    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.55/0.73  thf('14', plain,
% 0.55/0.73      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.55/0.73      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.55/0.73  thf('15', plain,
% 0.55/0.73      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.55/0.73      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.55/0.73  thf('16', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.55/0.73      inference('sup+', [status(thm)], ['14', '15'])).
% 0.55/0.73  thf('17', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('18', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (((X0) != (k1_xboole_0))
% 0.55/0.73          | ~ (v1_xboole_0 @ X0)
% 0.55/0.73          | ~ (v1_xboole_0 @ sk_B_1))),
% 0.55/0.73      inference('sup-', [status(thm)], ['16', '17'])).
% 0.55/0.73  thf('19', plain,
% 0.55/0.73      ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.55/0.73      inference('simplify', [status(thm)], ['18'])).
% 0.55/0.73  thf(d3_tarski, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( r1_tarski @ A @ B ) <=>
% 0.55/0.73       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.55/0.73  thf('20', plain,
% 0.55/0.73      (![X1 : $i, X3 : $i]:
% 0.55/0.73         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.73  thf('21', plain,
% 0.55/0.73      (![X1 : $i, X3 : $i]:
% 0.55/0.73         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.73  thf('22', plain,
% 0.55/0.73      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.55/0.73      inference('sup-', [status(thm)], ['20', '21'])).
% 0.55/0.73  thf('23', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.55/0.73      inference('simplify', [status(thm)], ['22'])).
% 0.55/0.73  thf(existence_m1_subset_1, axiom,
% 0.55/0.73    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.55/0.73  thf('24', plain, (![X6 : $i]: (m1_subset_1 @ (sk_B @ X6) @ X6)),
% 0.55/0.73      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.55/0.73  thf('25', plain,
% 0.55/0.73      (![X7 : $i, X8 : $i]:
% 0.55/0.73         ((r2_hidden @ X7 @ X8)
% 0.55/0.73          | (v1_xboole_0 @ X8)
% 0.55/0.73          | ~ (m1_subset_1 @ X7 @ X8))),
% 0.55/0.73      inference('cnf', [status(esa)], [t2_subset])).
% 0.55/0.73  thf('26', plain,
% 0.55/0.73      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.55/0.73      inference('sup-', [status(thm)], ['24', '25'])).
% 0.55/0.73  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.55/0.73  thf('27', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.55/0.73      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.55/0.73  thf('28', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         (~ (r2_hidden @ X0 @ X1)
% 0.55/0.73          | (r2_hidden @ X0 @ X2)
% 0.55/0.73          | ~ (r1_tarski @ X1 @ X2))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.73  thf('29', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.55/0.73      inference('sup-', [status(thm)], ['27', '28'])).
% 0.55/0.73  thf('30', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         ((v1_xboole_0 @ k1_xboole_0) | (r2_hidden @ (sk_B @ k1_xboole_0) @ X0))),
% 0.55/0.73      inference('sup-', [status(thm)], ['26', '29'])).
% 0.55/0.73  thf(t7_ordinal1, axiom,
% 0.55/0.73    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.55/0.73  thf('31', plain,
% 0.55/0.73      (![X13 : $i, X14 : $i]:
% 0.55/0.73         (~ (r2_hidden @ X13 @ X14) | ~ (r1_tarski @ X14 @ X13))),
% 0.55/0.73      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.55/0.73  thf('32', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         ((v1_xboole_0 @ k1_xboole_0)
% 0.55/0.73          | ~ (r1_tarski @ X0 @ (sk_B @ k1_xboole_0)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['30', '31'])).
% 0.55/0.73  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.55/0.73      inference('sup-', [status(thm)], ['23', '32'])).
% 0.55/0.73  thf('34', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.55/0.73      inference('demod', [status(thm)], ['19', '33'])).
% 0.55/0.73  thf('35', plain,
% 0.55/0.73      (((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ 
% 0.55/0.73         (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D))
% 0.55/0.73        | ((sk_C_1) = (k1_xboole_0)))),
% 0.55/0.73      inference('clc', [status(thm)], ['13', '34'])).
% 0.55/0.73  thf('36', plain,
% 0.55/0.73      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.55/0.73        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('37', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         (~ (r2_hidden @ X0 @ X1)
% 0.55/0.73          | (r2_hidden @ X0 @ X2)
% 0.55/0.73          | ~ (r1_tarski @ X1 @ X2))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.73  thf('38', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         ((r2_hidden @ X0 @ (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))
% 0.55/0.73          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['36', '37'])).
% 0.55/0.73  thf('39', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(redefinition_k1_relset_1, axiom,
% 0.55/0.73    (![A:$i,B:$i,C:$i]:
% 0.55/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.73       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.55/0.73  thf('40', plain,
% 0.55/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.55/0.73         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.55/0.73          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.55/0.73      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.55/0.73  thf('41', plain,
% 0.55/0.73      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.55/0.73      inference('sup-', [status(thm)], ['39', '40'])).
% 0.55/0.73  thf('42', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 0.55/0.73          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.55/0.73      inference('demod', [status(thm)], ['38', '41'])).
% 0.55/0.73  thf('43', plain,
% 0.55/0.73      ((((sk_C_1) = (k1_xboole_0))
% 0.55/0.73        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['35', '42'])).
% 0.55/0.73  thf(d8_partfun1, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.55/0.73       ( ![C:$i]:
% 0.55/0.73         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.55/0.73           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.55/0.73  thf('44', plain,
% 0.55/0.73      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.55/0.73         (~ (r2_hidden @ X21 @ (k1_relat_1 @ X22))
% 0.55/0.73          | ((k7_partfun1 @ X23 @ X22 @ X21) = (k1_funct_1 @ X22 @ X21))
% 0.55/0.73          | ~ (v1_funct_1 @ X22)
% 0.55/0.73          | ~ (v5_relat_1 @ X22 @ X23)
% 0.55/0.73          | ~ (v1_relat_1 @ X22))),
% 0.55/0.73      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.55/0.73  thf('45', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (((sk_C_1) = (k1_xboole_0))
% 0.55/0.73          | ~ (v1_relat_1 @ sk_E)
% 0.55/0.73          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.55/0.73          | ~ (v1_funct_1 @ sk_E)
% 0.55/0.73          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.55/0.73              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['43', '44'])).
% 0.55/0.73  thf('46', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(cc2_relat_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( v1_relat_1 @ A ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.55/0.73  thf('47', plain,
% 0.55/0.73      (![X9 : $i, X10 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.55/0.73          | (v1_relat_1 @ X9)
% 0.55/0.73          | ~ (v1_relat_1 @ X10))),
% 0.55/0.73      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.55/0.73  thf('48', plain,
% 0.55/0.73      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) | (v1_relat_1 @ sk_E))),
% 0.55/0.73      inference('sup-', [status(thm)], ['46', '47'])).
% 0.55/0.73  thf(fc6_relat_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.55/0.73  thf('49', plain,
% 0.55/0.73      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.55/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.55/0.73  thf('50', plain, ((v1_relat_1 @ sk_E)),
% 0.55/0.73      inference('demod', [status(thm)], ['48', '49'])).
% 0.55/0.73  thf('51', plain, ((v1_funct_1 @ sk_E)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('52', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (((sk_C_1) = (k1_xboole_0))
% 0.55/0.73          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.55/0.73          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.55/0.73              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.55/0.73      inference('demod', [status(thm)], ['45', '50', '51'])).
% 0.55/0.73  thf('53', plain,
% 0.55/0.73      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.55/0.73          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.55/0.73        | ((sk_C_1) = (k1_xboole_0)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['3', '52'])).
% 0.55/0.73  thf('54', plain,
% 0.55/0.73      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.55/0.73         sk_F) != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('55', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('56', plain,
% 0.55/0.73      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.55/0.73      inference('sup-', [status(thm)], ['39', '40'])).
% 0.55/0.73  thf('57', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(t185_funct_2, axiom,
% 0.55/0.73    (![A:$i,B:$i,C:$i]:
% 0.55/0.73     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.55/0.73       ( ![D:$i]:
% 0.55/0.73         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.55/0.73             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.55/0.73           ( ![E:$i]:
% 0.55/0.73             ( ( ( v1_funct_1 @ E ) & 
% 0.55/0.73                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.55/0.73               ( ![F:$i]:
% 0.55/0.73                 ( ( m1_subset_1 @ F @ B ) =>
% 0.55/0.73                   ( ( r1_tarski @
% 0.55/0.73                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.55/0.73                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.55/0.73                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.55/0.73                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.55/0.73                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.73  thf('58', plain,
% 0.55/0.73      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.55/0.73         (~ (v1_funct_1 @ X24)
% 0.55/0.73          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.55/0.73          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.55/0.73          | ~ (m1_subset_1 @ X27 @ X25)
% 0.55/0.73          | ((k1_funct_1 @ (k8_funct_2 @ X25 @ X26 @ X29 @ X24 @ X28) @ X27)
% 0.55/0.73              = (k1_funct_1 @ X28 @ (k1_funct_1 @ X24 @ X27)))
% 0.55/0.73          | ((X25) = (k1_xboole_0))
% 0.55/0.73          | ~ (r1_tarski @ (k2_relset_1 @ X25 @ X26 @ X24) @ 
% 0.55/0.73               (k1_relset_1 @ X26 @ X29 @ X28))
% 0.55/0.73          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X29)))
% 0.55/0.73          | ~ (v1_funct_1 @ X28)
% 0.55/0.73          | (v1_xboole_0 @ X26))),
% 0.55/0.73      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.55/0.73  thf('59', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         ((v1_xboole_0 @ sk_C_1)
% 0.55/0.73          | ~ (v1_funct_1 @ X0)
% 0.55/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.55/0.73          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.55/0.73               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.55/0.73          | ((sk_B_1) = (k1_xboole_0))
% 0.55/0.73          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.55/0.73              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.55/0.73          | ~ (m1_subset_1 @ X2 @ sk_B_1)
% 0.55/0.73          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 0.55/0.73          | ~ (v1_funct_1 @ sk_D))),
% 0.55/0.73      inference('sup-', [status(thm)], ['57', '58'])).
% 0.55/0.73  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('62', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         ((v1_xboole_0 @ sk_C_1)
% 0.55/0.73          | ~ (v1_funct_1 @ X0)
% 0.55/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.55/0.73          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.55/0.73               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.55/0.73          | ((sk_B_1) = (k1_xboole_0))
% 0.55/0.73          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.55/0.73              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.55/0.73          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 0.55/0.73      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.55/0.73  thf('63', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('64', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         ((v1_xboole_0 @ sk_C_1)
% 0.55/0.73          | ~ (v1_funct_1 @ X0)
% 0.55/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 0.55/0.73          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.55/0.73               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 0.55/0.73          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 0.55/0.73              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.55/0.73          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 0.55/0.73      inference('simplify_reflect-', [status(thm)], ['62', '63'])).
% 0.55/0.73  thf('65', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.55/0.73             (k1_relat_1 @ sk_E))
% 0.55/0.73          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.55/0.73          | ((k1_funct_1 @ 
% 0.55/0.73              (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.55/0.73              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.55/0.73          | ~ (m1_subset_1 @ sk_E @ 
% 0.55/0.73               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 0.55/0.73          | ~ (v1_funct_1 @ sk_E)
% 0.55/0.73          | (v1_xboole_0 @ sk_C_1))),
% 0.55/0.73      inference('sup-', [status(thm)], ['56', '64'])).
% 0.55/0.73  thf('66', plain,
% 0.55/0.73      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.55/0.73        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('67', plain,
% 0.55/0.73      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.55/0.73      inference('sup-', [status(thm)], ['39', '40'])).
% 0.55/0.73  thf('68', plain,
% 0.55/0.73      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.55/0.73        (k1_relat_1 @ sk_E))),
% 0.55/0.73      inference('demod', [status(thm)], ['66', '67'])).
% 0.55/0.73  thf('69', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('70', plain, ((v1_funct_1 @ sk_E)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('71', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.55/0.73          | ((k1_funct_1 @ 
% 0.55/0.73              (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.55/0.73              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.55/0.73          | (v1_xboole_0 @ sk_C_1))),
% 0.55/0.73      inference('demod', [status(thm)], ['65', '68', '69', '70'])).
% 0.55/0.73  thf('72', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('73', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.55/0.73            X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.55/0.73          | ~ (m1_subset_1 @ X0 @ sk_B_1))),
% 0.55/0.73      inference('clc', [status(thm)], ['71', '72'])).
% 0.55/0.73  thf('74', plain,
% 0.55/0.73      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.55/0.73         sk_F) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['55', '73'])).
% 0.55/0.73  thf('75', plain,
% 0.55/0.73      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.55/0.73         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.55/0.73      inference('demod', [status(thm)], ['54', '74'])).
% 0.55/0.73  thf('76', plain,
% 0.55/0.73      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.55/0.73          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.55/0.73        | ((sk_C_1) = (k1_xboole_0)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['53', '75'])).
% 0.55/0.73  thf('77', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.55/0.73      inference('simplify', [status(thm)], ['76'])).
% 0.55/0.73  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.55/0.73      inference('sup-', [status(thm)], ['23', '32'])).
% 0.55/0.73  thf('79', plain, ($false),
% 0.55/0.73      inference('demod', [status(thm)], ['0', '77', '78'])).
% 0.55/0.73  
% 0.55/0.73  % SZS output end Refutation
% 0.55/0.73  
% 0.55/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

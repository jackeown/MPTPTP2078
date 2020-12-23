%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fFiwpNdTAn

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:08 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 243 expanded)
%              Number of leaves         :   43 (  90 expanded)
%              Depth                    :   17
%              Number of atoms          : 1294 (5104 expanded)
%              Number of equality atoms :   78 ( 232 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('11',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(clc,[status(thm)],['3','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_relat_1 @ E )
            & ( v1_funct_1 @ E ) )
         => ( ( r2_hidden @ C @ A )
           => ( ( B = k1_xboole_0 )
              | ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C )
                = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ~ ( v1_funct_1 @ X36 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X37 @ X36 ) @ X38 )
        = ( k1_funct_1 @ X36 @ ( k1_funct_1 @ X37 @ X38 ) ) )
      | ( X39 = k1_xboole_0 )
      | ~ ( r2_hidden @ X38 @ X40 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_2])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( sk_C = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( sk_C = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ sk_F )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(clc,[status(thm)],['3','11'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('25',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ X41 @ X42 )
      | ( X43 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X44 @ X41 ) @ ( k2_relset_1 @ X42 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
      | ~ ( v1_funct_1 @ sk_D )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('29',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','29','30','31'])).

thf('33',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['23','32'])).

thf('34',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('37',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('41',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['33','44'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('46',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k1_relat_1 @ X28 ) )
      | ( ( k7_partfun1 @ X29 @ X28 @ X27 )
        = ( k1_funct_1 @ X28 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v5_relat_1 @ X28 @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_C = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('49',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('52',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_C = k1_xboole_0 )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['47','52','53'])).

thf('55',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','54'])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) )
           => ( ( B = k1_xboole_0 )
              | ( ( k8_funct_2 @ A @ B @ C @ D @ E )
                = ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) )).

thf('58',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k8_funct_2 @ X25 @ X23 @ X24 @ X26 @ X22 )
        = ( k1_partfun1 @ X25 @ X23 @ X23 @ X24 @ X26 @ X22 ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X25 @ X23 @ X26 ) @ ( k1_relset_1 @ X23 @ X24 @ X22 ) )
      | ( X23 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X25 @ X23 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d12_funct_2])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('61',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
    | ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('66',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('68',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('71',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 )
        = ( k5_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','68','77','78','79','80'])).

thf('82',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','83'])).

thf('85',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['50','51'])).

thf('89',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['0','90','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fFiwpNdTAn
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:47:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.52/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.70  % Solved by: fo/fo7.sh
% 0.52/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.70  % done 458 iterations in 0.253s
% 0.52/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.70  % SZS output start Refutation
% 0.52/0.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.52/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.52/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.70  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.52/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.70  thf(sk_E_type, type, sk_E: $i).
% 0.52/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.70  thf(sk_D_type, type, sk_D: $i).
% 0.52/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.70  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.52/0.70  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.52/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.70  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.52/0.70  thf(sk_F_type, type, sk_F: $i).
% 0.52/0.70  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.52/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.52/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.70  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.52/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.70  thf(t186_funct_2, conjecture,
% 0.52/0.70    (![A:$i,B:$i,C:$i]:
% 0.52/0.70     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.52/0.70       ( ![D:$i]:
% 0.52/0.70         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.52/0.70             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.52/0.70           ( ![E:$i]:
% 0.52/0.70             ( ( ( v1_funct_1 @ E ) & 
% 0.52/0.70                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.52/0.70               ( ![F:$i]:
% 0.52/0.70                 ( ( m1_subset_1 @ F @ B ) =>
% 0.52/0.70                   ( ( r1_tarski @
% 0.52/0.70                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.52/0.70                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.52/0.70                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.52/0.70                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.52/0.70                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.70    (~( ![A:$i,B:$i,C:$i]:
% 0.52/0.70        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.52/0.70          ( ![D:$i]:
% 0.52/0.70            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.52/0.70                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.52/0.70              ( ![E:$i]:
% 0.52/0.70                ( ( ( v1_funct_1 @ E ) & 
% 0.52/0.70                    ( m1_subset_1 @
% 0.52/0.70                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.52/0.70                  ( ![F:$i]:
% 0.52/0.70                    ( ( m1_subset_1 @ F @ B ) =>
% 0.52/0.70                      ( ( r1_tarski @
% 0.52/0.70                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.52/0.70                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.52/0.70                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.52/0.70                          ( ( k1_funct_1 @
% 0.52/0.70                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.52/0.70                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.52/0.70    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 0.52/0.70  thf('0', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(t2_subset, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( m1_subset_1 @ A @ B ) =>
% 0.52/0.70       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.52/0.70  thf('2', plain,
% 0.52/0.70      (![X4 : $i, X5 : $i]:
% 0.52/0.70         ((r2_hidden @ X4 @ X5)
% 0.52/0.70          | (v1_xboole_0 @ X5)
% 0.52/0.70          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.52/0.70      inference('cnf', [status(esa)], [t2_subset])).
% 0.52/0.70  thf('3', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.52/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.52/0.70  thf(l13_xboole_0, axiom,
% 0.52/0.70    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.52/0.70  thf('4', plain,
% 0.52/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.70  thf('5', plain,
% 0.52/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.70  thf('6', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.52/0.70      inference('sup+', [status(thm)], ['4', '5'])).
% 0.52/0.70  thf('7', plain, (((sk_B) != (k1_xboole_0))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('8', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (((X0) != (k1_xboole_0))
% 0.52/0.70          | ~ (v1_xboole_0 @ X0)
% 0.52/0.70          | ~ (v1_xboole_0 @ sk_B))),
% 0.52/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.52/0.70  thf('9', plain, ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.52/0.70      inference('simplify', [status(thm)], ['8'])).
% 0.52/0.70  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.52/0.70  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.70  thf('11', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.52/0.70      inference('simplify_reflect+', [status(thm)], ['9', '10'])).
% 0.52/0.70  thf('12', plain, ((r2_hidden @ sk_F @ sk_B)),
% 0.52/0.70      inference('clc', [status(thm)], ['3', '11'])).
% 0.52/0.70  thf('13', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(t21_funct_2, axiom,
% 0.52/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.70     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.52/0.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.70       ( ![E:$i]:
% 0.52/0.70         ( ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) ) =>
% 0.52/0.70           ( ( r2_hidden @ C @ A ) =>
% 0.52/0.70             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.52/0.70               ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C ) =
% 0.52/0.70                 ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) ))).
% 0.52/0.70  thf('14', plain,
% 0.52/0.70      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X36)
% 0.52/0.70          | ~ (v1_funct_1 @ X36)
% 0.52/0.70          | ((k1_funct_1 @ (k5_relat_1 @ X37 @ X36) @ X38)
% 0.52/0.70              = (k1_funct_1 @ X36 @ (k1_funct_1 @ X37 @ X38)))
% 0.52/0.70          | ((X39) = (k1_xboole_0))
% 0.52/0.70          | ~ (r2_hidden @ X38 @ X40)
% 0.52/0.70          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.52/0.70          | ~ (v1_funct_2 @ X37 @ X40 @ X39)
% 0.52/0.70          | ~ (v1_funct_1 @ X37))),
% 0.52/0.70      inference('cnf', [status(esa)], [t21_funct_2])).
% 0.52/0.70  thf('15', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (~ (v1_funct_1 @ sk_D)
% 0.52/0.70          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.52/0.70          | ~ (r2_hidden @ X0 @ sk_B)
% 0.52/0.70          | ((sk_C) = (k1_xboole_0))
% 0.52/0.70          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.52/0.70              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.52/0.70          | ~ (v1_funct_1 @ X1)
% 0.52/0.70          | ~ (v1_relat_1 @ X1))),
% 0.52/0.70      inference('sup-', [status(thm)], ['13', '14'])).
% 0.52/0.70  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('17', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('18', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (~ (r2_hidden @ X0 @ sk_B)
% 0.52/0.70          | ((sk_C) = (k1_xboole_0))
% 0.52/0.70          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.52/0.70              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.52/0.70          | ~ (v1_funct_1 @ X1)
% 0.52/0.70          | ~ (v1_relat_1 @ X1))),
% 0.52/0.70      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.52/0.70  thf('19', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X0)
% 0.52/0.70          | ~ (v1_funct_1 @ X0)
% 0.52/0.70          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_F)
% 0.52/0.70              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.52/0.70          | ((sk_C) = (k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['12', '18'])).
% 0.52/0.70  thf('20', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(cc2_relset_1, axiom,
% 0.52/0.70    (![A:$i,B:$i,C:$i]:
% 0.52/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.52/0.70  thf('21', plain,
% 0.52/0.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.52/0.70         ((v5_relat_1 @ X13 @ X15)
% 0.52/0.70          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.52/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.52/0.70  thf('22', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 0.52/0.70      inference('sup-', [status(thm)], ['20', '21'])).
% 0.52/0.70  thf('23', plain, ((r2_hidden @ sk_F @ sk_B)),
% 0.52/0.70      inference('clc', [status(thm)], ['3', '11'])).
% 0.52/0.70  thf('24', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(t6_funct_2, axiom,
% 0.52/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.70     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.52/0.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.70       ( ( r2_hidden @ C @ A ) =>
% 0.52/0.70         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.52/0.70           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.52/0.70  thf('25', plain,
% 0.52/0.70      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.52/0.70         (~ (r2_hidden @ X41 @ X42)
% 0.52/0.70          | ((X43) = (k1_xboole_0))
% 0.52/0.70          | ~ (v1_funct_1 @ X44)
% 0.52/0.70          | ~ (v1_funct_2 @ X44 @ X42 @ X43)
% 0.52/0.70          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.52/0.70          | (r2_hidden @ (k1_funct_1 @ X44 @ X41) @ 
% 0.52/0.70             (k2_relset_1 @ X42 @ X43 @ X44)))),
% 0.52/0.70      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.52/0.70  thf('26', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.52/0.70           (k2_relset_1 @ sk_B @ sk_C @ sk_D))
% 0.52/0.70          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.52/0.70          | ~ (v1_funct_1 @ sk_D)
% 0.52/0.70          | ((sk_C) = (k1_xboole_0))
% 0.52/0.70          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.52/0.70      inference('sup-', [status(thm)], ['24', '25'])).
% 0.52/0.70  thf('27', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(redefinition_k2_relset_1, axiom,
% 0.52/0.70    (![A:$i,B:$i,C:$i]:
% 0.52/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.70       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.52/0.70  thf('28', plain,
% 0.52/0.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.52/0.70         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 0.52/0.70          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.52/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.52/0.70  thf('29', plain,
% 0.52/0.70      (((k2_relset_1 @ sk_B @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.52/0.70      inference('sup-', [status(thm)], ['27', '28'])).
% 0.52/0.70  thf('30', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('31', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('32', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))
% 0.52/0.70          | ((sk_C) = (k1_xboole_0))
% 0.52/0.70          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.52/0.70      inference('demod', [status(thm)], ['26', '29', '30', '31'])).
% 0.52/0.70  thf('33', plain,
% 0.52/0.70      ((((sk_C) = (k1_xboole_0))
% 0.52/0.70        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k2_relat_1 @ sk_D)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['23', '32'])).
% 0.52/0.70  thf('34', plain,
% 0.52/0.70      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.52/0.70        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(t3_subset, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.52/0.70  thf('35', plain,
% 0.52/0.70      (![X6 : $i, X8 : $i]:
% 0.52/0.70         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.52/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.70  thf('36', plain,
% 0.52/0.70      ((m1_subset_1 @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.52/0.70        (k1_zfmisc_1 @ (k1_relset_1 @ sk_C @ sk_A @ sk_E)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['34', '35'])).
% 0.52/0.70  thf(l3_subset_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.52/0.70  thf('37', plain,
% 0.52/0.70      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.70         (~ (r2_hidden @ X1 @ X2)
% 0.52/0.70          | (r2_hidden @ X1 @ X3)
% 0.52/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.52/0.70      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.52/0.70  thf('38', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((r2_hidden @ X0 @ (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 0.52/0.70          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['36', '37'])).
% 0.52/0.70  thf('39', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(redefinition_k1_relset_1, axiom,
% 0.52/0.70    (![A:$i,B:$i,C:$i]:
% 0.52/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.52/0.70  thf('40', plain,
% 0.52/0.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.52/0.70         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.52/0.70          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.52/0.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.52/0.70  thf('41', plain,
% 0.52/0.70      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.52/0.70      inference('sup-', [status(thm)], ['39', '40'])).
% 0.52/0.70  thf('42', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 0.52/0.70          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 0.52/0.70      inference('demod', [status(thm)], ['38', '41'])).
% 0.52/0.70  thf('43', plain,
% 0.52/0.70      (((k2_relset_1 @ sk_B @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.52/0.70      inference('sup-', [status(thm)], ['27', '28'])).
% 0.52/0.70  thf('44', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 0.52/0.70          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 0.52/0.70      inference('demod', [status(thm)], ['42', '43'])).
% 0.52/0.70  thf('45', plain,
% 0.52/0.70      ((((sk_C) = (k1_xboole_0))
% 0.52/0.70        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['33', '44'])).
% 0.52/0.70  thf(d8_partfun1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.52/0.70       ( ![C:$i]:
% 0.52/0.70         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.52/0.70           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.52/0.70  thf('46', plain,
% 0.52/0.70      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.52/0.70         (~ (r2_hidden @ X27 @ (k1_relat_1 @ X28))
% 0.52/0.70          | ((k7_partfun1 @ X29 @ X28 @ X27) = (k1_funct_1 @ X28 @ X27))
% 0.52/0.70          | ~ (v1_funct_1 @ X28)
% 0.52/0.70          | ~ (v5_relat_1 @ X28 @ X29)
% 0.52/0.70          | ~ (v1_relat_1 @ X28))),
% 0.52/0.70      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.52/0.70  thf('47', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (((sk_C) = (k1_xboole_0))
% 0.52/0.70          | ~ (v1_relat_1 @ sk_E)
% 0.52/0.70          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.52/0.70          | ~ (v1_funct_1 @ sk_E)
% 0.52/0.70          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.52/0.70              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.52/0.70  thf('48', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(cc2_relat_1, axiom,
% 0.52/0.70    (![A:$i]:
% 0.52/0.70     ( ( v1_relat_1 @ A ) =>
% 0.52/0.70       ( ![B:$i]:
% 0.52/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.52/0.70  thf('49', plain,
% 0.52/0.70      (![X9 : $i, X10 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.52/0.70          | (v1_relat_1 @ X9)
% 0.52/0.70          | ~ (v1_relat_1 @ X10))),
% 0.52/0.70      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.52/0.70  thf('50', plain,
% 0.52/0.70      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_E))),
% 0.52/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.52/0.70  thf(fc6_relat_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.52/0.70  thf('51', plain,
% 0.52/0.70      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.52/0.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.52/0.70  thf('52', plain, ((v1_relat_1 @ sk_E)),
% 0.52/0.70      inference('demod', [status(thm)], ['50', '51'])).
% 0.52/0.70  thf('53', plain, ((v1_funct_1 @ sk_E)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('54', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (((sk_C) = (k1_xboole_0))
% 0.52/0.70          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.52/0.70          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.52/0.70              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.52/0.70      inference('demod', [status(thm)], ['47', '52', '53'])).
% 0.52/0.70  thf('55', plain,
% 0.52/0.70      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.52/0.70          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.52/0.70        | ((sk_C) = (k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['22', '54'])).
% 0.52/0.70  thf('56', plain,
% 0.52/0.70      (((k2_relset_1 @ sk_B @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.52/0.70      inference('sup-', [status(thm)], ['27', '28'])).
% 0.52/0.70  thf('57', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(d12_funct_2, axiom,
% 0.52/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.70     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.52/0.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.70       ( ![E:$i]:
% 0.52/0.70         ( ( ( v1_funct_1 @ E ) & 
% 0.52/0.70             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.52/0.70           ( ( r1_tarski @
% 0.52/0.70               ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) ) =>
% 0.52/0.70             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.52/0.70               ( ( k8_funct_2 @ A @ B @ C @ D @ E ) =
% 0.52/0.70                 ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) ))).
% 0.52/0.70  thf('58', plain,
% 0.52/0.70      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.52/0.70         (~ (v1_funct_1 @ X22)
% 0.52/0.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.52/0.70          | ((k8_funct_2 @ X25 @ X23 @ X24 @ X26 @ X22)
% 0.52/0.70              = (k1_partfun1 @ X25 @ X23 @ X23 @ X24 @ X26 @ X22))
% 0.52/0.70          | ~ (r1_tarski @ (k2_relset_1 @ X25 @ X23 @ X26) @ 
% 0.52/0.70               (k1_relset_1 @ X23 @ X24 @ X22))
% 0.52/0.70          | ((X23) = (k1_xboole_0))
% 0.52/0.70          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 0.52/0.70          | ~ (v1_funct_2 @ X26 @ X25 @ X23)
% 0.52/0.70          | ~ (v1_funct_1 @ X26))),
% 0.52/0.70      inference('cnf', [status(esa)], [d12_funct_2])).
% 0.52/0.70  thf('59', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (~ (v1_funct_1 @ X0)
% 0.52/0.70          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 0.52/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 0.52/0.70          | ((sk_C) = (k1_xboole_0))
% 0.52/0.70          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ 
% 0.52/0.70               (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 0.52/0.70          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 0.52/0.70              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E))
% 0.52/0.70          | ~ (v1_funct_1 @ sk_E))),
% 0.52/0.70      inference('sup-', [status(thm)], ['57', '58'])).
% 0.52/0.70  thf('60', plain,
% 0.52/0.70      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.52/0.70      inference('sup-', [status(thm)], ['39', '40'])).
% 0.52/0.70  thf('61', plain, ((v1_funct_1 @ sk_E)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('62', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (~ (v1_funct_1 @ X0)
% 0.52/0.70          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 0.52/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 0.52/0.70          | ((sk_C) = (k1_xboole_0))
% 0.52/0.70          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ (k1_relat_1 @ sk_E))
% 0.52/0.70          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 0.52/0.70              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E)))),
% 0.52/0.70      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.52/0.70  thf('63', plain,
% 0.52/0.70      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))
% 0.52/0.70        | ((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.52/0.70            = (k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E))
% 0.52/0.70        | ((sk_C) = (k1_xboole_0))
% 0.52/0.70        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))
% 0.52/0.70        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.52/0.70        | ~ (v1_funct_1 @ sk_D))),
% 0.52/0.70      inference('sup-', [status(thm)], ['56', '62'])).
% 0.52/0.70  thf('64', plain,
% 0.52/0.70      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.52/0.70        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('65', plain,
% 0.52/0.70      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.52/0.70      inference('sup-', [status(thm)], ['39', '40'])).
% 0.52/0.70  thf('66', plain,
% 0.52/0.70      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.52/0.70      inference('demod', [status(thm)], ['64', '65'])).
% 0.52/0.70  thf('67', plain,
% 0.52/0.70      (((k2_relset_1 @ sk_B @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.52/0.70      inference('sup-', [status(thm)], ['27', '28'])).
% 0.52/0.70  thf('68', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.52/0.70      inference('demod', [status(thm)], ['66', '67'])).
% 0.52/0.70  thf('69', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('70', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(redefinition_k1_partfun1, axiom,
% 0.52/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.52/0.70     ( ( ( v1_funct_1 @ E ) & 
% 0.52/0.70         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.52/0.70         ( v1_funct_1 @ F ) & 
% 0.52/0.70         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.52/0.70       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.52/0.70  thf('71', plain,
% 0.52/0.70      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.52/0.70          | ~ (v1_funct_1 @ X30)
% 0.52/0.70          | ~ (v1_funct_1 @ X33)
% 0.52/0.70          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.52/0.70          | ((k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33)
% 0.52/0.70              = (k5_relat_1 @ X30 @ X33)))),
% 0.52/0.70      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.52/0.70  thf('72', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 0.52/0.70            = (k5_relat_1 @ sk_D @ X0))
% 0.52/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.52/0.70          | ~ (v1_funct_1 @ X0)
% 0.52/0.70          | ~ (v1_funct_1 @ sk_D))),
% 0.52/0.70      inference('sup-', [status(thm)], ['70', '71'])).
% 0.52/0.70  thf('73', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('74', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 0.52/0.70            = (k5_relat_1 @ sk_D @ X0))
% 0.52/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.52/0.70          | ~ (v1_funct_1 @ X0))),
% 0.52/0.70      inference('demod', [status(thm)], ['72', '73'])).
% 0.52/0.70  thf('75', plain,
% 0.52/0.70      ((~ (v1_funct_1 @ sk_E)
% 0.52/0.70        | ((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.52/0.70            = (k5_relat_1 @ sk_D @ sk_E)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['69', '74'])).
% 0.52/0.70  thf('76', plain, ((v1_funct_1 @ sk_E)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('77', plain,
% 0.52/0.70      (((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.52/0.70         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.52/0.70      inference('demod', [status(thm)], ['75', '76'])).
% 0.52/0.70  thf('78', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('79', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('80', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('81', plain,
% 0.52/0.70      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.52/0.70          = (k5_relat_1 @ sk_D @ sk_E))
% 0.52/0.70        | ((sk_C) = (k1_xboole_0)))),
% 0.52/0.70      inference('demod', [status(thm)], ['63', '68', '77', '78', '79', '80'])).
% 0.52/0.70  thf('82', plain,
% 0.52/0.70      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.52/0.70         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('83', plain,
% 0.52/0.70      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.52/0.70          != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.52/0.70        | ((sk_C) = (k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['81', '82'])).
% 0.52/0.70  thf('84', plain,
% 0.52/0.70      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.52/0.70          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.52/0.70        | ((sk_C) = (k1_xboole_0))
% 0.52/0.70        | ((sk_C) = (k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['55', '83'])).
% 0.52/0.70  thf('85', plain,
% 0.52/0.70      ((((sk_C) = (k1_xboole_0))
% 0.52/0.70        | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.52/0.70            != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.52/0.70      inference('simplify', [status(thm)], ['84'])).
% 0.52/0.70  thf('86', plain,
% 0.52/0.70      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.52/0.70          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 0.52/0.70        | ((sk_C) = (k1_xboole_0))
% 0.52/0.70        | ~ (v1_funct_1 @ sk_E)
% 0.52/0.70        | ~ (v1_relat_1 @ sk_E)
% 0.52/0.70        | ((sk_C) = (k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['19', '85'])).
% 0.52/0.70  thf('87', plain, ((v1_funct_1 @ sk_E)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('88', plain, ((v1_relat_1 @ sk_E)),
% 0.52/0.70      inference('demod', [status(thm)], ['50', '51'])).
% 0.52/0.70  thf('89', plain,
% 0.52/0.70      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.52/0.70          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 0.52/0.70        | ((sk_C) = (k1_xboole_0))
% 0.52/0.70        | ((sk_C) = (k1_xboole_0)))),
% 0.52/0.70      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.52/0.70  thf('90', plain, (((sk_C) = (k1_xboole_0))),
% 0.52/0.70      inference('simplify', [status(thm)], ['89'])).
% 0.52/0.70  thf('91', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.70  thf('92', plain, ($false),
% 0.52/0.70      inference('demod', [status(thm)], ['0', '90', '91'])).
% 0.52/0.70  
% 0.52/0.70  % SZS output end Refutation
% 0.52/0.70  
% 0.52/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

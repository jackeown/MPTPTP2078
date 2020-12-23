%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DHnGMHf0nP

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 154 expanded)
%              Number of leaves         :   28 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  877 (3354 expanded)
%              Number of equality atoms :   52 ( 109 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t75_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ B )
              & ( ( k2_relset_1 @ A @ A @ B )
                = A ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ B )
                & ( ( k2_relset_1 @ A @ A @ B )
                  = A ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X27: $i] :
      ( ( k6_partfun1 @ X27 )
      = ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X28 @ X29 )
        = X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X28 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('5',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['5','6','7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('14',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t44_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = A ) )
           => ( B
              = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ X1 @ X0 )
       != X1 )
      | ( ( k2_relat_1 @ X1 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t44_funct_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k5_relat_1 @ sk_B @ X0 )
       != sk_B )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ sk_B @ X0 )
       != sk_B )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','21','22'])).

thf('24',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_C
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
    | ( ( k5_relat_1 @ sk_B @ sk_C )
     != sk_B ) ),
    inference('sup-',[status(thm)],['11','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['5','6','7','10'])).

thf('30',plain,
    ( ( sk_A != sk_A )
    | ( sk_C
      = ( k6_relat_1 @ sk_A ) )
    | ( ( k5_relat_1 @ sk_B @ sk_C )
     != sk_B ) ),
    inference(demod,[status(thm)],['24','27','28','29'])).

thf('31',plain,
    ( ( ( k5_relat_1 @ sk_B @ sk_C )
     != sk_B )
    | ( sk_C
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 )
        = ( k5_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = ( k5_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('43',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X16 @ X17 @ X19 @ X20 @ X15 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('50',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( X11 = X14 )
      | ~ ( r2_relset_1 @ X12 @ X13 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = sk_B ) ),
    inference('sup-',[status(thm)],['40','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( sk_B
    = ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['38','39','54'])).

thf('56',plain,
    ( ( sk_B != sk_B )
    | ( sk_C
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','55'])).

thf('57',plain,
    ( sk_C
    = ( k6_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( r2_relset_1 @ X12 @ X13 @ X11 @ X14 )
      | ( X11 != X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('60',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_relset_1 @ X12 @ X13 @ X14 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['2','57','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DHnGMHf0nP
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:46:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 161 iterations in 0.093s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.54  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.21/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.54  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.21/0.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.54  thf(t75_funct_2, conjecture,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.54       ( ![C:$i]:
% 0.21/0.54         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.21/0.54             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.54           ( ( ( r2_relset_1 @
% 0.21/0.54                 A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ B ) & 
% 0.21/0.54               ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) ) =>
% 0.21/0.54             ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i]:
% 0.21/0.54        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.54            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.54          ( ![C:$i]:
% 0.21/0.54            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.21/0.54                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.54              ( ( ( r2_relset_1 @
% 0.21/0.54                    A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ B ) & 
% 0.21/0.54                  ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) ) =>
% 0.21/0.54                ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t75_funct_2])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k6_partfun1, axiom,
% 0.21/0.54    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.54  thf('1', plain, (![X27 : $i]: ((k6_partfun1 @ X27) = (k6_relat_1 @ X27))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.54  thf('2', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t67_funct_2, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.54       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (![X28 : $i, X29 : $i]:
% 0.21/0.54         (((k1_relset_1 @ X28 @ X28 @ X29) = (X28))
% 0.21/0.54          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))
% 0.21/0.54          | ~ (v1_funct_2 @ X29 @ X28 @ X28)
% 0.21/0.54          | ~ (v1_funct_1 @ X29))),
% 0.21/0.54      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.54        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.21/0.54        | ((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.54  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('7', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.54         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 0.21/0.54          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.54  thf('11', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.54         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.21/0.54          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.54  thf('15', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('16', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.54      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.54  thf(t44_funct_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.54           ( ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.21/0.54               ( ( k5_relat_1 @ A @ B ) = ( A ) ) ) =>
% 0.21/0.54             ( ( B ) = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.21/0.54          | ((k5_relat_1 @ X1 @ X0) != (X1))
% 0.21/0.54          | ((k2_relat_1 @ X1) != (k1_relat_1 @ X0))
% 0.21/0.54          | ~ (v1_funct_1 @ X1)
% 0.21/0.54          | ~ (v1_relat_1 @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [t44_funct_1])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((sk_A) != (k1_relat_1 @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ sk_B)
% 0.21/0.54          | ~ (v1_funct_1 @ sk_B)
% 0.21/0.54          | ((k5_relat_1 @ sk_B @ X0) != (sk_B))
% 0.21/0.54          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(cc1_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( v1_relat_1 @ C ) ))).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.54         ((v1_relat_1 @ X2)
% 0.21/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.54  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.54  thf('22', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((sk_A) != (k1_relat_1 @ X0))
% 0.21/0.54          | ((k5_relat_1 @ sk_B @ X0) != (sk_B))
% 0.21/0.54          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['18', '21', '22'])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      ((((sk_A) != (sk_A))
% 0.21/0.54        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.54        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.54        | ((sk_C) = (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 0.21/0.54        | ((k5_relat_1 @ sk_B @ sk_C) != (sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['11', '23'])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.54         ((v1_relat_1 @ X2)
% 0.21/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.54  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.54  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('29', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      ((((sk_A) != (sk_A))
% 0.21/0.54        | ((sk_C) = (k6_relat_1 @ sk_A))
% 0.21/0.54        | ((k5_relat_1 @ sk_B @ sk_C) != (sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['24', '27', '28', '29'])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      ((((k5_relat_1 @ sk_B @ sk_C) != (sk_B)) | ((sk_C) = (k6_relat_1 @ sk_A)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k1_partfun1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.54     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.54         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.54         ( v1_funct_1 @ F ) & 
% 0.21/0.54         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.21/0.54       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.21/0.54          | ~ (v1_funct_1 @ X21)
% 0.21/0.54          | ~ (v1_funct_1 @ X24)
% 0.21/0.54          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.21/0.54          | ((k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24)
% 0.21/0.54              = (k5_relat_1 @ X21 @ X24)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.21/0.54            = (k5_relat_1 @ sk_B @ X0))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.54  thf('36', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.21/0.54            = (k5_relat_1 @ sk_B @ X0))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.54          | ~ (v1_funct_1 @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.54        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.21/0.54            = (k5_relat_1 @ sk_B @ sk_C)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['32', '37'])).
% 0.21/0.54  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.54        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_k1_partfun1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.54     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.54         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.54         ( v1_funct_1 @ F ) & 
% 0.21/0.54         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.21/0.54       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.21/0.54         ( m1_subset_1 @
% 0.21/0.54           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.21/0.54           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.21/0.54          | ~ (v1_funct_1 @ X15)
% 0.21/0.54          | ~ (v1_funct_1 @ X18)
% 0.21/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.21/0.54          | (m1_subset_1 @ (k1_partfun1 @ X16 @ X17 @ X19 @ X20 @ X15 @ X18) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X20))))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.21/0.54          | ~ (v1_funct_1 @ X1)
% 0.21/0.54          | ~ (v1_funct_1 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.54  thf('45', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.21/0.54          | ~ (v1_funct_1 @ X1))),
% 0.21/0.54      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.54        | (m1_subset_1 @ 
% 0.21/0.54           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['41', '46'])).
% 0.21/0.54  thf('48', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      ((m1_subset_1 @ 
% 0.21/0.54        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.54  thf(redefinition_r2_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.54       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.21/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.21/0.54          | ((X11) = (X14))
% 0.21/0.54          | ~ (r2_relset_1 @ X12 @ X13 @ X11 @ X14))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.54             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ X0)
% 0.21/0.54          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) = (X0))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.54        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) = (sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['40', '51'])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.54  thf('55', plain, (((sk_B) = (k5_relat_1 @ sk_B @ sk_C))),
% 0.21/0.54      inference('demod', [status(thm)], ['38', '39', '54'])).
% 0.21/0.54  thf('56', plain, ((((sk_B) != (sk_B)) | ((sk_C) = (k6_relat_1 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['31', '55'])).
% 0.21/0.54  thf('57', plain, (((sk_C) = (k6_relat_1 @ sk_A))),
% 0.21/0.54      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.21/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.21/0.54          | (r2_relset_1 @ X12 @ X13 @ X11 @ X14)
% 0.21/0.54          | ((X11) != (X14)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.54         ((r2_relset_1 @ X12 @ X13 @ X14 @ X14)
% 0.21/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['59'])).
% 0.21/0.54  thf('61', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.21/0.54      inference('sup-', [status(thm)], ['58', '60'])).
% 0.21/0.54  thf('62', plain, ($false),
% 0.21/0.54      inference('demod', [status(thm)], ['2', '57', '61'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

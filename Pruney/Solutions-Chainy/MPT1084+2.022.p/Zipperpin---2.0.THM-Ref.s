%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T1jmfy2JOH

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:39 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 395 expanded)
%              Number of leaves         :   37 ( 136 expanded)
%              Depth                    :   15
%              Number of atoms          :  872 (5452 expanded)
%              Number of equality atoms :   69 ( 283 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t201_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ A @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ( ( k3_funct_2 @ A @ A @ B @ C )
                  = C ) )
           => ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ( v1_funct_1 @ B )
              & ( v1_funct_2 @ B @ A @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ A )
                 => ( ( k3_funct_2 @ A @ A @ B @ C )
                    = C ) )
             => ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t201_funct_2])).

thf('0',plain,(
    ~ ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
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

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ sk_A ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
       != X6 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 )
      | ( X7
        = ( k6_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('18',plain,(
    ! [X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ( r2_hidden @ ( sk_C @ X7 @ ( k1_relat_1 @ X7 ) ) @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('19',plain,(
    ! [X24: $i] :
      ( ( k6_partfun1 @ X24 )
      = ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('20',plain,(
    ! [X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k6_partfun1 @ ( k1_relat_1 @ X7 ) ) )
      | ( r2_hidden @ ( sk_C @ X7 @ ( k1_relat_1 @ X7 ) ) @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','20'])).

thf('22',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf('23',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf('24',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','29'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('32',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X29: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X29 )
        = X29 )
      | ~ ( m1_subset_1 @ X29 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      = ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ X21 )
      | ( ( k3_funct_2 @ X21 @ X22 @ X20 @ X23 )
        = ( k1_funct_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','44'])).

thf('46',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
       != X6 )
      | ( ( k1_funct_1 @ X7 @ ( sk_C @ X7 @ X6 ) )
       != ( sk_C @ X7 @ X6 ) )
      | ( X7
        = ( k6_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('49',plain,(
    ! [X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ( ( k1_funct_1 @ X7 @ ( sk_C @ X7 @ ( k1_relat_1 @ X7 ) ) )
       != ( sk_C @ X7 @ ( k1_relat_1 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X24: $i] :
      ( ( k6_partfun1 @ X24 )
      = ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('51',plain,(
    ! [X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k6_partfun1 @ ( k1_relat_1 @ X7 ) ) )
      | ( ( k1_funct_1 @ X7 @ ( sk_C @ X7 @ ( k1_relat_1 @ X7 ) ) )
       != ( sk_C @ X7 @ ( k1_relat_1 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
     != ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf('54',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf('55',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['27','28'])).

thf('57',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
     != ( sk_C @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('58',plain,
    ( sk_B
    = ( k6_partfun1 @ sk_A ) ),
    inference(clc,[status(thm)],['46','57'])).

thf('59',plain,(
    ~ ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['0','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('61',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( r2_funct_2 @ X26 @ X27 @ X25 @ X28 )
      | ( X25 != X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('62',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_funct_2 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['59','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T1jmfy2JOH
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 107 iterations in 0.103s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.57  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.38/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.38/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.38/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.57  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.38/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.38/0.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.38/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.57  thf(t201_funct_2, conjecture,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.38/0.57             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.38/0.57           ( ( ![C:$i]:
% 0.38/0.57               ( ( m1_subset_1 @ C @ A ) =>
% 0.38/0.57                 ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.38/0.57             ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i]:
% 0.38/0.57        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.57          ( ![B:$i]:
% 0.38/0.57            ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.38/0.57                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.38/0.57              ( ( ![C:$i]:
% 0.38/0.57                  ( ( m1_subset_1 @ C @ A ) =>
% 0.38/0.57                    ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.38/0.57                ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t201_funct_2])).
% 0.38/0.57  thf('0', plain, (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('1', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(d1_funct_2, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.38/0.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.38/0.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_1, axiom,
% 0.38/0.57    (![C:$i,B:$i,A:$i]:
% 0.38/0.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.38/0.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.57         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 0.38/0.57          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 0.38/0.57          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A)
% 0.38/0.57        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.57  thf(zf_stmt_2, axiom,
% 0.38/0.57    (![B:$i,A:$i]:
% 0.38/0.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.57       ( zip_tseitin_0 @ B @ A ) ))).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (![X12 : $i, X13 : $i]:
% 0.38/0.57         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.38/0.57  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.38/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.38/0.57  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.38/0.57  thf(zf_stmt_5, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.38/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.57         (~ (zip_tseitin_0 @ X17 @ X18)
% 0.38/0.57          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 0.38/0.57          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      (((zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      (((v1_xboole_0 @ sk_A) | (zip_tseitin_1 @ sk_B @ sk_A @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['6', '9'])).
% 0.38/0.57  thf('11', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('12', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.57      inference('clc', [status(thm)], ['10', '11'])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.57         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.38/0.57          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.57  thf('16', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.38/0.57      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.38/0.57  thf(t34_funct_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.57       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.38/0.57         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.38/0.57           ( ![C:$i]:
% 0.38/0.57             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X6 : $i, X7 : $i]:
% 0.38/0.57         (((k1_relat_1 @ X7) != (X6))
% 0.38/0.57          | (r2_hidden @ (sk_C @ X7 @ X6) @ X6)
% 0.38/0.57          | ((X7) = (k6_relat_1 @ X6))
% 0.38/0.57          | ~ (v1_funct_1 @ X7)
% 0.38/0.57          | ~ (v1_relat_1 @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (![X7 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X7)
% 0.38/0.57          | ~ (v1_funct_1 @ X7)
% 0.38/0.57          | ((X7) = (k6_relat_1 @ (k1_relat_1 @ X7)))
% 0.38/0.57          | (r2_hidden @ (sk_C @ X7 @ (k1_relat_1 @ X7)) @ (k1_relat_1 @ X7)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.57  thf(redefinition_k6_partfun1, axiom,
% 0.38/0.57    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.38/0.57  thf('19', plain, (![X24 : $i]: ((k6_partfun1 @ X24) = (k6_relat_1 @ X24))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (![X7 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X7)
% 0.38/0.57          | ~ (v1_funct_1 @ X7)
% 0.38/0.57          | ((X7) = (k6_partfun1 @ (k1_relat_1 @ X7)))
% 0.38/0.57          | (r2_hidden @ (sk_C @ X7 @ (k1_relat_1 @ X7)) @ (k1_relat_1 @ X7)))),
% 0.38/0.57      inference('demod', [status(thm)], ['18', '19'])).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      (((r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.38/0.57        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.38/0.57        | ~ (v1_funct_1 @ sk_B)
% 0.38/0.57        | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['16', '20'])).
% 0.38/0.57  thf('22', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.38/0.57      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.38/0.57  thf('23', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.38/0.57      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.38/0.57  thf('24', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(cc2_relat_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      (![X2 : $i, X3 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.38/0.57          | (v1_relat_1 @ X2)
% 0.38/0.57          | ~ (v1_relat_1 @ X3))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.57  thf(fc6_relat_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.57  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.57      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.57  thf('30', plain,
% 0.38/0.57      (((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.38/0.57        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['21', '22', '23', '24', '29'])).
% 0.38/0.57  thf(t1_subset, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [t1_subset])).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.38/0.57        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.57  thf('33', plain,
% 0.38/0.57      (![X29 : $i]:
% 0.38/0.57         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X29) = (X29))
% 0.38/0.57          | ~ (m1_subset_1 @ X29 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('34', plain,
% 0.38/0.57      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.38/0.57        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.38/0.57            = (sk_C @ sk_B @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.38/0.57        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.57  thf('36', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(redefinition_k3_funct_2, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.38/0.57         ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.57         ( m1_subset_1 @ D @ A ) ) =>
% 0.38/0.57       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.38/0.57  thf('37', plain,
% 0.38/0.57      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.38/0.57          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 0.38/0.57          | ~ (v1_funct_1 @ X20)
% 0.38/0.57          | (v1_xboole_0 @ X21)
% 0.38/0.57          | ~ (m1_subset_1 @ X23 @ X21)
% 0.38/0.57          | ((k3_funct_2 @ X21 @ X22 @ X20 @ X23) = (k1_funct_1 @ X20 @ X23)))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ sk_A)
% 0.38/0.57          | ~ (v1_funct_1 @ sk_B)
% 0.38/0.57          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.57  thf('39', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('40', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.38/0.57  thf('42', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('43', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.38/0.57          | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0)))),
% 0.38/0.57      inference('clc', [status(thm)], ['41', '42'])).
% 0.38/0.57  thf('44', plain,
% 0.38/0.57      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.38/0.57        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.38/0.57            = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['35', '43'])).
% 0.38/0.57  thf('45', plain,
% 0.38/0.57      ((((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)))
% 0.38/0.57        | ((sk_B) = (k6_partfun1 @ sk_A))
% 0.38/0.57        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['34', '44'])).
% 0.38/0.57  thf('46', plain,
% 0.38/0.57      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.38/0.57        | ((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.38/0.57      inference('simplify', [status(thm)], ['45'])).
% 0.38/0.57  thf('47', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.38/0.57      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.38/0.57  thf('48', plain,
% 0.38/0.57      (![X6 : $i, X7 : $i]:
% 0.38/0.57         (((k1_relat_1 @ X7) != (X6))
% 0.38/0.57          | ((k1_funct_1 @ X7 @ (sk_C @ X7 @ X6)) != (sk_C @ X7 @ X6))
% 0.38/0.57          | ((X7) = (k6_relat_1 @ X6))
% 0.38/0.57          | ~ (v1_funct_1 @ X7)
% 0.38/0.57          | ~ (v1_relat_1 @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.38/0.57  thf('49', plain,
% 0.38/0.57      (![X7 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X7)
% 0.38/0.57          | ~ (v1_funct_1 @ X7)
% 0.38/0.57          | ((X7) = (k6_relat_1 @ (k1_relat_1 @ X7)))
% 0.38/0.57          | ((k1_funct_1 @ X7 @ (sk_C @ X7 @ (k1_relat_1 @ X7)))
% 0.38/0.57              != (sk_C @ X7 @ (k1_relat_1 @ X7))))),
% 0.38/0.57      inference('simplify', [status(thm)], ['48'])).
% 0.38/0.57  thf('50', plain, (![X24 : $i]: ((k6_partfun1 @ X24) = (k6_relat_1 @ X24))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.38/0.57  thf('51', plain,
% 0.38/0.57      (![X7 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X7)
% 0.38/0.57          | ~ (v1_funct_1 @ X7)
% 0.38/0.57          | ((X7) = (k6_partfun1 @ (k1_relat_1 @ X7)))
% 0.38/0.57          | ((k1_funct_1 @ X7 @ (sk_C @ X7 @ (k1_relat_1 @ X7)))
% 0.38/0.57              != (sk_C @ X7 @ (k1_relat_1 @ X7))))),
% 0.38/0.57      inference('demod', [status(thm)], ['49', '50'])).
% 0.38/0.57  thf('52', plain,
% 0.38/0.57      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.38/0.57          != (sk_C @ sk_B @ (k1_relat_1 @ sk_B)))
% 0.38/0.57        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.38/0.57        | ~ (v1_funct_1 @ sk_B)
% 0.38/0.57        | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['47', '51'])).
% 0.38/0.57  thf('53', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.38/0.57      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.38/0.57  thf('54', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.38/0.57      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.38/0.57  thf('55', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.57      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.57  thf('57', plain,
% 0.38/0.57      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)) != (sk_C @ sk_B @ sk_A))
% 0.38/0.57        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 0.38/0.57  thf('58', plain, (((sk_B) = (k6_partfun1 @ sk_A))),
% 0.38/0.57      inference('clc', [status(thm)], ['46', '57'])).
% 0.38/0.57  thf('59', plain, (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.38/0.57      inference('demod', [status(thm)], ['0', '58'])).
% 0.38/0.57  thf('60', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(redefinition_r2_funct_2, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.57         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.57       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.38/0.57  thf('61', plain,
% 0.38/0.57      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.38/0.57          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 0.38/0.57          | ~ (v1_funct_1 @ X25)
% 0.38/0.57          | ~ (v1_funct_1 @ X28)
% 0.38/0.57          | ~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.38/0.57          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.38/0.57          | (r2_funct_2 @ X26 @ X27 @ X25 @ X28)
% 0.38/0.57          | ((X25) != (X28)))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.38/0.57  thf('62', plain,
% 0.38/0.57      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.38/0.57         ((r2_funct_2 @ X26 @ X27 @ X28 @ X28)
% 0.38/0.57          | ~ (v1_funct_1 @ X28)
% 0.38/0.57          | ~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.38/0.57          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.38/0.57      inference('simplify', [status(thm)], ['61'])).
% 0.38/0.57  thf('63', plain,
% 0.38/0.57      ((~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.57        | ~ (v1_funct_1 @ sk_B)
% 0.38/0.57        | (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['60', '62'])).
% 0.38/0.57  thf('64', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('65', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('66', plain, ((r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.38/0.57      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.38/0.57  thf('67', plain, ($false), inference('demod', [status(thm)], ['59', '66'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.41/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q6aXGI0sLq

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 452 expanded)
%              Number of leaves         :   36 ( 153 expanded)
%              Depth                    :   14
%              Number of atoms          :  896 (6397 expanded)
%              Number of equality atoms :   71 ( 331 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

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

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('5',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['6','11'])).

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
    ! [X3: $i,X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
       != X3 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 )
      | ( X4
        = ( k6_relat_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('18',plain,(
    ! [X4: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ( r2_hidden @ ( sk_C @ X4 @ ( k1_relat_1 @ X4 ) ) @ ( k1_relat_1 @ X4 ) ) ) ),
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
    ! [X4: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ( r2_hidden @ ( sk_C @ X4 @ ( k1_relat_1 @ X4 ) ) @ ( k1_relat_1 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( m1_subset_1 @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['16','22'])).

thf('24',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf('25',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf('31',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25','28','29','30'])).

thf('32',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X29: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X29 )
        = X29 )
      | ~ ( m1_subset_1 @ X29 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      = ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ X21 )
      | ( ( k3_funct_2 @ X21 @ X22 @ X20 @ X23 )
        = ( k1_funct_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','45'])).

thf('47',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf('49',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
       != X3 )
      | ( ( k1_funct_1 @ X4 @ ( sk_C @ X4 @ X3 ) )
       != ( sk_C @ X4 @ X3 ) )
      | ( X4
        = ( k6_relat_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('50',plain,(
    ! [X4: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ( ( k1_funct_1 @ X4 @ ( sk_C @ X4 @ ( k1_relat_1 @ X4 ) ) )
       != ( sk_C @ X4 @ ( k1_relat_1 @ X4 ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X24: $i] :
      ( ( k6_partfun1 @ X24 )
      = ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('52',plain,(
    ! [X4: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ( ( k1_funct_1 @ X4 @ ( sk_C @ X4 @ ( k1_relat_1 @ X4 ) ) )
       != ( sk_C @ X4 @ ( k1_relat_1 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
     != ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf('55',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf('56',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['26','27'])).

thf('58',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
     != ( sk_C @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,
    ( sk_B
    = ( k6_partfun1 @ sk_A ) ),
    inference(clc,[status(thm)],['47','58'])).

thf('60',plain,(
    ~ ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['0','59'])).

thf('61',plain,(
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

thf('62',plain,(
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

thf('63',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_funct_2 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['60','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q6aXGI0sLq
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:25:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.59  % Solved by: fo/fo7.sh
% 0.20/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.59  % done 126 iterations in 0.152s
% 0.20/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.59  % SZS output start Refutation
% 0.20/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.59  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.20/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.59  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.20/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.59  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.59  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.20/0.59  thf(t201_funct_2, conjecture,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.59             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.59           ( ( ![C:$i]:
% 0.20/0.59               ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.59                 ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.20/0.59             ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 0.20/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.59    (~( ![A:$i]:
% 0.20/0.59        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.59          ( ![B:$i]:
% 0.20/0.59            ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.59                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.59              ( ( ![C:$i]:
% 0.20/0.59                  ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.59                    ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.20/0.59                ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 0.20/0.59    inference('cnf.neg', [status(esa)], [t201_funct_2])).
% 0.20/0.59  thf('0', plain, (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('1', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(d1_funct_2, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.59  thf(zf_stmt_1, axiom,
% 0.41/0.59    (![C:$i,B:$i,A:$i]:
% 0.41/0.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.41/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.41/0.59  thf('2', plain,
% 0.41/0.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.59         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 0.41/0.59          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 0.41/0.59          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.59  thf('3', plain,
% 0.41/0.59      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A)
% 0.41/0.59        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.59  thf('4', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.41/0.59  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.41/0.59  thf(zf_stmt_4, axiom,
% 0.41/0.59    (![B:$i,A:$i]:
% 0.41/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.59       ( zip_tseitin_0 @ B @ A ) ))).
% 0.41/0.59  thf(zf_stmt_5, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.41/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.41/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.41/0.59         (~ (zip_tseitin_0 @ X17 @ X18)
% 0.41/0.59          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 0.41/0.59          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.41/0.59  thf('6', plain,
% 0.41/0.59      (((zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.59  thf('7', plain,
% 0.41/0.59      (![X12 : $i, X13 : $i]:
% 0.41/0.59         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.41/0.59  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.41/0.59  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.59  thf('9', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.41/0.59      inference('sup+', [status(thm)], ['7', '8'])).
% 0.41/0.59  thf('10', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('11', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0)),
% 0.41/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.41/0.59  thf('12', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ sk_A)),
% 0.41/0.59      inference('demod', [status(thm)], ['6', '11'])).
% 0.41/0.59  thf('13', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.41/0.59  thf('14', plain,
% 0.41/0.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.59         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.41/0.59          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.59  thf('15', plain,
% 0.41/0.59      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.41/0.59      inference('sup-', [status(thm)], ['13', '14'])).
% 0.41/0.59  thf('16', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.41/0.59  thf(t34_funct_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.59       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.41/0.59         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.41/0.59           ( ![C:$i]:
% 0.41/0.59             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.41/0.59  thf('17', plain,
% 0.41/0.59      (![X3 : $i, X4 : $i]:
% 0.41/0.59         (((k1_relat_1 @ X4) != (X3))
% 0.41/0.59          | (r2_hidden @ (sk_C @ X4 @ X3) @ X3)
% 0.41/0.59          | ((X4) = (k6_relat_1 @ X3))
% 0.41/0.59          | ~ (v1_funct_1 @ X4)
% 0.41/0.59          | ~ (v1_relat_1 @ X4))),
% 0.41/0.59      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      (![X4 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X4)
% 0.41/0.59          | ~ (v1_funct_1 @ X4)
% 0.41/0.59          | ((X4) = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.41/0.59          | (r2_hidden @ (sk_C @ X4 @ (k1_relat_1 @ X4)) @ (k1_relat_1 @ X4)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['17'])).
% 0.41/0.59  thf(redefinition_k6_partfun1, axiom,
% 0.41/0.59    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.41/0.59  thf('19', plain, (![X24 : $i]: ((k6_partfun1 @ X24) = (k6_relat_1 @ X24))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.41/0.59  thf('20', plain,
% 0.41/0.59      (![X4 : $i]:
% 0.41/0.59         (~ (v1_relat_1 @ X4)
% 0.41/0.59          | ~ (v1_funct_1 @ X4)
% 0.41/0.59          | ((X4) = (k6_partfun1 @ (k1_relat_1 @ X4)))
% 0.41/0.59          | (r2_hidden @ (sk_C @ X4 @ (k1_relat_1 @ X4)) @ (k1_relat_1 @ X4)))),
% 0.41/0.59      inference('demod', [status(thm)], ['18', '19'])).
% 0.41/0.59  thf(d2_subset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( v1_xboole_0 @ A ) =>
% 0.41/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.41/0.59       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.59  thf('21', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X0 @ X1)
% 0.41/0.59          | (m1_subset_1 @ X0 @ X1)
% 0.41/0.59          | (v1_xboole_0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (((X0) = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.41/0.59          | ~ (v1_funct_1 @ X0)
% 0.41/0.59          | ~ (v1_relat_1 @ X0)
% 0.41/0.59          | (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.41/0.59          | (m1_subset_1 @ (sk_C @ X0 @ (k1_relat_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.41/0.59  thf('23', plain,
% 0.41/0.59      (((m1_subset_1 @ (sk_C @ sk_B @ (k1_relat_1 @ sk_B)) @ sk_A)
% 0.41/0.59        | (v1_xboole_0 @ (k1_relat_1 @ sk_B))
% 0.41/0.59        | ~ (v1_relat_1 @ sk_B)
% 0.41/0.59        | ~ (v1_funct_1 @ sk_B)
% 0.41/0.59        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B))))),
% 0.41/0.59      inference('sup+', [status(thm)], ['16', '22'])).
% 0.41/0.59  thf('24', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.41/0.59  thf('25', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.41/0.59  thf('26', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(cc1_relset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59       ( v1_relat_1 @ C ) ))).
% 0.41/0.59  thf('27', plain,
% 0.41/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.41/0.59         ((v1_relat_1 @ X6)
% 0.41/0.59          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.41/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.41/0.59  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.41/0.59  thf('29', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('30', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.41/0.59  thf('31', plain,
% 0.41/0.59      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.41/0.59        | (v1_xboole_0 @ sk_A)
% 0.41/0.59        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['23', '24', '25', '28', '29', '30'])).
% 0.41/0.59  thf('32', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('33', plain,
% 0.41/0.59      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.41/0.59        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.41/0.60      inference('clc', [status(thm)], ['31', '32'])).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      (![X29 : $i]:
% 0.41/0.60         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X29) = (X29))
% 0.41/0.60          | ~ (m1_subset_1 @ X29 @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.41/0.60        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.41/0.60            = (sk_C @ sk_B @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['33', '34'])).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.41/0.60        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.41/0.60      inference('clc', [status(thm)], ['31', '32'])).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(redefinition_k3_funct_2, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.60     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.41/0.60         ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.41/0.60         ( m1_subset_1 @ D @ A ) ) =>
% 0.41/0.60       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.41/0.60          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 0.41/0.60          | ~ (v1_funct_1 @ X20)
% 0.41/0.60          | (v1_xboole_0 @ X21)
% 0.41/0.60          | ~ (m1_subset_1 @ X23 @ X21)
% 0.41/0.60          | ((k3_funct_2 @ X21 @ X22 @ X20 @ X23) = (k1_funct_1 @ X20 @ X23)))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.41/0.60  thf('39', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.41/0.60          | (v1_xboole_0 @ sk_A)
% 0.41/0.60          | ~ (v1_funct_1 @ sk_B)
% 0.41/0.60          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.41/0.60  thf('40', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('41', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('42', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.41/0.60          | (v1_xboole_0 @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.41/0.60  thf('43', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('44', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.41/0.60          | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0)))),
% 0.41/0.60      inference('clc', [status(thm)], ['42', '43'])).
% 0.41/0.60  thf('45', plain,
% 0.41/0.60      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.41/0.60        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.41/0.60            = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['36', '44'])).
% 0.41/0.60  thf('46', plain,
% 0.41/0.60      ((((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)))
% 0.41/0.60        | ((sk_B) = (k6_partfun1 @ sk_A))
% 0.41/0.60        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['35', '45'])).
% 0.41/0.60  thf('47', plain,
% 0.41/0.60      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.41/0.60        | ((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.41/0.60      inference('simplify', [status(thm)], ['46'])).
% 0.41/0.60  thf('48', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.41/0.60  thf('49', plain,
% 0.41/0.60      (![X3 : $i, X4 : $i]:
% 0.41/0.60         (((k1_relat_1 @ X4) != (X3))
% 0.41/0.60          | ((k1_funct_1 @ X4 @ (sk_C @ X4 @ X3)) != (sk_C @ X4 @ X3))
% 0.41/0.60          | ((X4) = (k6_relat_1 @ X3))
% 0.41/0.60          | ~ (v1_funct_1 @ X4)
% 0.41/0.60          | ~ (v1_relat_1 @ X4))),
% 0.41/0.60      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.41/0.60  thf('50', plain,
% 0.41/0.60      (![X4 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X4)
% 0.41/0.60          | ~ (v1_funct_1 @ X4)
% 0.41/0.60          | ((X4) = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.41/0.60          | ((k1_funct_1 @ X4 @ (sk_C @ X4 @ (k1_relat_1 @ X4)))
% 0.41/0.60              != (sk_C @ X4 @ (k1_relat_1 @ X4))))),
% 0.41/0.60      inference('simplify', [status(thm)], ['49'])).
% 0.41/0.60  thf('51', plain, (![X24 : $i]: ((k6_partfun1 @ X24) = (k6_relat_1 @ X24))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.41/0.60  thf('52', plain,
% 0.41/0.60      (![X4 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X4)
% 0.41/0.60          | ~ (v1_funct_1 @ X4)
% 0.41/0.60          | ((X4) = (k6_partfun1 @ (k1_relat_1 @ X4)))
% 0.41/0.60          | ((k1_funct_1 @ X4 @ (sk_C @ X4 @ (k1_relat_1 @ X4)))
% 0.41/0.60              != (sk_C @ X4 @ (k1_relat_1 @ X4))))),
% 0.41/0.60      inference('demod', [status(thm)], ['50', '51'])).
% 0.41/0.60  thf('53', plain,
% 0.41/0.60      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.41/0.60          != (sk_C @ sk_B @ (k1_relat_1 @ sk_B)))
% 0.41/0.60        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.41/0.60        | ~ (v1_funct_1 @ sk_B)
% 0.41/0.60        | ~ (v1_relat_1 @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['48', '52'])).
% 0.41/0.60  thf('54', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.41/0.60  thf('55', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.41/0.60  thf('56', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('57', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.41/0.60  thf('58', plain,
% 0.41/0.60      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)) != (sk_C @ sk_B @ sk_A))
% 0.41/0.60        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.41/0.60      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 0.41/0.60  thf('59', plain, (((sk_B) = (k6_partfun1 @ sk_A))),
% 0.41/0.60      inference('clc', [status(thm)], ['47', '58'])).
% 0.41/0.60  thf('60', plain, (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.41/0.60      inference('demod', [status(thm)], ['0', '59'])).
% 0.41/0.60  thf('61', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(redefinition_r2_funct_2, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.41/0.60         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.60       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.41/0.60  thf('62', plain,
% 0.41/0.60      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.41/0.60          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 0.41/0.60          | ~ (v1_funct_1 @ X25)
% 0.41/0.60          | ~ (v1_funct_1 @ X28)
% 0.41/0.60          | ~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.41/0.60          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.41/0.60          | (r2_funct_2 @ X26 @ X27 @ X25 @ X28)
% 0.41/0.60          | ((X25) != (X28)))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.41/0.60  thf('63', plain,
% 0.41/0.60      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.41/0.60         ((r2_funct_2 @ X26 @ X27 @ X28 @ X28)
% 0.41/0.60          | ~ (v1_funct_1 @ X28)
% 0.41/0.60          | ~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.41/0.60          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.41/0.60      inference('simplify', [status(thm)], ['62'])).
% 0.41/0.60  thf('64', plain,
% 0.41/0.60      ((~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.41/0.60        | ~ (v1_funct_1 @ sk_B)
% 0.41/0.60        | (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['61', '63'])).
% 0.41/0.60  thf('65', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('66', plain, ((v1_funct_1 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('67', plain, ((r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.41/0.60      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.41/0.60  thf('68', plain, ($false), inference('demod', [status(thm)], ['60', '67'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

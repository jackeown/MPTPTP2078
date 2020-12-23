%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.quHYYOtKWq

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 368 expanded)
%              Number of leaves         :   35 ( 124 expanded)
%              Depth                    :   14
%              Number of atoms          :  866 (4974 expanded)
%              Number of equality atoms :   70 ( 292 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ( X13
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( zip_tseitin_1 @ X15 @ X14 @ X13 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 )
      | ( zip_tseitin_1 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('9',plain,(
    ! [X11: $i] :
      ( zip_tseitin_0 @ X11 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['10'])).

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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ( ( k1_relat_1 @ X3 )
       != X2 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 )
      | ( X3
        = ( k6_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('18',plain,(
    ! [X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( X3
        = ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k1_relat_1 @ X3 ) ) @ ( k1_relat_1 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('19',plain,(
    ! [X23: $i] :
      ( ( k6_partfun1 @ X23 )
      = ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('20',plain,(
    ! [X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( X3
        = ( k6_partfun1 @ ( k1_relat_1 @ X3 ) ) )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k1_relat_1 @ X3 ) ) @ ( k1_relat_1 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['16','22'])).

thf('24',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf('30',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','27','28','29'])).

thf('31',plain,(
    ! [X28: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X28 )
        = X28 )
      | ~ ( m1_subset_1 @ X28 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      = ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','27','28','29'])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ X20 )
      | ( ( k3_funct_2 @ X20 @ X21 @ X19 @ X22 )
        = ( k1_funct_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','42'])).

thf('44',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k1_relat_1 @ X3 )
       != X2 )
      | ( ( k1_funct_1 @ X3 @ ( sk_C @ X3 @ X2 ) )
       != ( sk_C @ X3 @ X2 ) )
      | ( X3
        = ( k6_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('47',plain,(
    ! [X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( X3
        = ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) )
      | ( ( k1_funct_1 @ X3 @ ( sk_C @ X3 @ ( k1_relat_1 @ X3 ) ) )
       != ( sk_C @ X3 @ ( k1_relat_1 @ X3 ) ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X23: $i] :
      ( ( k6_partfun1 @ X23 )
      = ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('49',plain,(
    ! [X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( X3
        = ( k6_partfun1 @ ( k1_relat_1 @ X3 ) ) )
      | ( ( k1_funct_1 @ X3 @ ( sk_C @ X3 @ ( k1_relat_1 @ X3 ) ) )
       != ( sk_C @ X3 @ ( k1_relat_1 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
     != ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','49'])).

thf('51',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf('52',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','12','15'])).

thf('53',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf('55',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
     != ( sk_C @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('56',plain,
    ( sk_B
    = ( k6_partfun1 @ sk_A ) ),
    inference(clc,[status(thm)],['44','55'])).

thf('57',plain,(
    ~ ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['0','56'])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( r2_funct_2 @ X25 @ X26 @ X24 @ X27 )
      | ( X24 != X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('60',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_funct_2 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['57','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.quHYYOtKWq
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 107 iterations in 0.108s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.56  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.21/0.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.56  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.21/0.56  thf(t201_funct_2, conjecture,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.56             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.56           ( ( ![C:$i]:
% 0.21/0.56               ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.56                 ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.21/0.56             ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i]:
% 0.21/0.56        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.56          ( ![B:$i]:
% 0.21/0.56            ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.56                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.56              ( ( ![C:$i]:
% 0.21/0.56                  ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.56                    ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.21/0.56                ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t201_funct_2])).
% 0.21/0.56  thf('0', plain, (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(d1_funct_2, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.56           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.56             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.56           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.56             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_1, axiom,
% 0.21/0.56    (![C:$i,B:$i,A:$i]:
% 0.21/0.56     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.56       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.56         (~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.21/0.56          | ((X13) = (k1_relset_1 @ X13 @ X14 @ X15))
% 0.21/0.56          | ~ (zip_tseitin_1 @ X15 @ X14 @ X13))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A)
% 0.21/0.56        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.56  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.56  thf(zf_stmt_4, axiom,
% 0.21/0.56    (![B:$i,A:$i]:
% 0.21/0.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.56       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.56  thf(zf_stmt_5, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.56         (~ (zip_tseitin_0 @ X16 @ X17)
% 0.21/0.56          | (zip_tseitin_1 @ X18 @ X16 @ X17)
% 0.21/0.56          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (((zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X11 : $i, X12 : $i]:
% 0.21/0.56         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X11 : $i, X12 : $i]:
% 0.21/0.56         ((zip_tseitin_0 @ X11 @ X12) | ((X12) != (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.56  thf('9', plain, (![X11 : $i]: (zip_tseitin_0 @ X11 @ k1_xboole_0)),
% 0.21/0.56      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.21/0.56      inference('sup+', [status(thm)], ['7', '9'])).
% 0.21/0.56  thf('11', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.21/0.56      inference('eq_fact', [status(thm)], ['10'])).
% 0.21/0.56  thf('12', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)], ['6', '11'])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.56         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.21/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.56  thf('16', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.21/0.56  thf(t34_funct_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.56       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.21/0.56         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X2 : $i, X3 : $i]:
% 0.21/0.56         (((k1_relat_1 @ X3) != (X2))
% 0.21/0.56          | (r2_hidden @ (sk_C @ X3 @ X2) @ X2)
% 0.21/0.56          | ((X3) = (k6_relat_1 @ X2))
% 0.21/0.56          | ~ (v1_funct_1 @ X3)
% 0.21/0.56          | ~ (v1_relat_1 @ X3))),
% 0.21/0.56      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X3 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X3)
% 0.21/0.56          | ~ (v1_funct_1 @ X3)
% 0.21/0.56          | ((X3) = (k6_relat_1 @ (k1_relat_1 @ X3)))
% 0.21/0.56          | (r2_hidden @ (sk_C @ X3 @ (k1_relat_1 @ X3)) @ (k1_relat_1 @ X3)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.56  thf(redefinition_k6_partfun1, axiom,
% 0.21/0.56    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.56  thf('19', plain, (![X23 : $i]: ((k6_partfun1 @ X23) = (k6_relat_1 @ X23))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (![X3 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X3)
% 0.21/0.56          | ~ (v1_funct_1 @ X3)
% 0.21/0.56          | ((X3) = (k6_partfun1 @ (k1_relat_1 @ X3)))
% 0.21/0.56          | (r2_hidden @ (sk_C @ X3 @ (k1_relat_1 @ X3)) @ (k1_relat_1 @ X3)))),
% 0.21/0.56      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.56  thf(t1_subset, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((X0) = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ X0)
% 0.21/0.56          | (m1_subset_1 @ (sk_C @ X0 @ (k1_relat_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (((m1_subset_1 @ (sk_C @ sk_B @ (k1_relat_1 @ sk_B)) @ sk_A)
% 0.21/0.56        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.56        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.56        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['16', '22'])).
% 0.21/0.56  thf('24', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(cc1_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( v1_relat_1 @ C ) ))).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.56         ((v1_relat_1 @ X5)
% 0.21/0.56          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.56  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.56  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('29', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.56        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['23', '24', '27', '28', '29'])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      (![X28 : $i]:
% 0.21/0.56         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X28) = (X28))
% 0.21/0.56          | ~ (m1_subset_1 @ X28 @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.21/0.56        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.21/0.56            = (sk_C @ sk_B @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.56        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['23', '24', '27', '28', '29'])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(redefinition_k3_funct_2, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.56         ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.56         ( m1_subset_1 @ D @ A ) ) =>
% 0.21/0.56       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.21/0.56          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 0.21/0.56          | ~ (v1_funct_1 @ X19)
% 0.21/0.56          | (v1_xboole_0 @ X20)
% 0.21/0.56          | ~ (m1_subset_1 @ X22 @ X20)
% 0.21/0.56          | ((k3_funct_2 @ X20 @ X21 @ X19 @ X22) = (k1_funct_1 @ X19 @ X22)))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.56          | (v1_xboole_0 @ sk_A)
% 0.21/0.56          | ~ (v1_funct_1 @ sk_B)
% 0.21/0.56          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.56  thf('37', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('38', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.56          | (v1_xboole_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.21/0.56  thf('40', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.56          | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0)))),
% 0.21/0.56      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.21/0.56        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.21/0.56            = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['33', '41'])).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      ((((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)))
% 0.21/0.56        | ((sk_B) = (k6_partfun1 @ sk_A))
% 0.21/0.56        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['32', '42'])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.21/0.56        | ((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.56  thf('45', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.21/0.56  thf('46', plain,
% 0.21/0.56      (![X2 : $i, X3 : $i]:
% 0.21/0.56         (((k1_relat_1 @ X3) != (X2))
% 0.21/0.56          | ((k1_funct_1 @ X3 @ (sk_C @ X3 @ X2)) != (sk_C @ X3 @ X2))
% 0.21/0.56          | ((X3) = (k6_relat_1 @ X2))
% 0.21/0.56          | ~ (v1_funct_1 @ X3)
% 0.21/0.56          | ~ (v1_relat_1 @ X3))),
% 0.21/0.56      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      (![X3 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X3)
% 0.21/0.56          | ~ (v1_funct_1 @ X3)
% 0.21/0.56          | ((X3) = (k6_relat_1 @ (k1_relat_1 @ X3)))
% 0.21/0.56          | ((k1_funct_1 @ X3 @ (sk_C @ X3 @ (k1_relat_1 @ X3)))
% 0.21/0.56              != (sk_C @ X3 @ (k1_relat_1 @ X3))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.56  thf('48', plain, (![X23 : $i]: ((k6_partfun1 @ X23) = (k6_relat_1 @ X23))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      (![X3 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X3)
% 0.21/0.56          | ~ (v1_funct_1 @ X3)
% 0.21/0.56          | ((X3) = (k6_partfun1 @ (k1_relat_1 @ X3)))
% 0.21/0.56          | ((k1_funct_1 @ X3 @ (sk_C @ X3 @ (k1_relat_1 @ X3)))
% 0.21/0.56              != (sk_C @ X3 @ (k1_relat_1 @ X3))))),
% 0.21/0.56      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.21/0.56          != (sk_C @ sk_B @ (k1_relat_1 @ sk_B)))
% 0.21/0.56        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.21/0.56        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.56        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['45', '49'])).
% 0.21/0.56  thf('51', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.21/0.56  thf('52', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['3', '12', '15'])).
% 0.21/0.56  thf('53', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('54', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.56  thf('55', plain,
% 0.21/0.56      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)) != (sk_C @ sk_B @ sk_A))
% 0.21/0.56        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.21/0.56  thf('56', plain, (((sk_B) = (k6_partfun1 @ sk_A))),
% 0.21/0.56      inference('clc', [status(thm)], ['44', '55'])).
% 0.21/0.56  thf('57', plain, (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.21/0.56      inference('demod', [status(thm)], ['0', '56'])).
% 0.21/0.56  thf('58', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(redefinition_r2_funct_2, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.56         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.56       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.21/0.56  thf('59', plain,
% 0.21/0.56      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.21/0.56          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.21/0.56          | ~ (v1_funct_1 @ X24)
% 0.21/0.56          | ~ (v1_funct_1 @ X27)
% 0.21/0.56          | ~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.21/0.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.21/0.56          | (r2_funct_2 @ X25 @ X26 @ X24 @ X27)
% 0.21/0.56          | ((X24) != (X27)))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.21/0.56  thf('60', plain,
% 0.21/0.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.56         ((r2_funct_2 @ X25 @ X26 @ X27 @ X27)
% 0.21/0.56          | ~ (v1_funct_1 @ X27)
% 0.21/0.56          | ~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.21/0.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['59'])).
% 0.21/0.56  thf('61', plain,
% 0.21/0.56      ((~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.56        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.56        | (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['58', '60'])).
% 0.21/0.56  thf('62', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('63', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('64', plain, ((r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.21/0.56      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.21/0.56  thf('65', plain, ($false), inference('demod', [status(thm)], ['57', '64'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
